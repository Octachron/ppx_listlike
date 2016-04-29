(* Forked from the compiler libs implementation *)
module StringMap= Map.Make(String)

let cookies = ref StringMap.empty
let tool_name_ref = ref "";
					
open Parsetree
open Longident
open Asttypes
open Ast_helper
open Location

let lid name = { txt = Lident name; loc = Location.none }

  let make_string x = Exp.constant (Pconst_string (x, None))

  let make_bool x =
    if x
    then Exp.construct (lid "true") None
    else Exp.construct (lid "false") None

  let rec make_list f lst =
    match lst with
    | x :: rest ->
      Exp.construct (lid "::") (Some (Exp.tuple [f x; make_list f rest]))
    | [] ->
      Exp.construct (lid "[]") None

  let make_pair f1 f2 (x1, x2) =
    Exp.tuple [f1 x1; f2 x2]

  let make_option f opt =
    match opt with
    | Some x -> Exp.construct (lid "Some") (Some (f x))
    | None   -> Exp.construct (lid "None") None

  let get_cookies () =
    lid "cookies",
    make_list (make_pair make_string (fun x -> x))
      (StringMap.bindings !cookies)

  let mk fields =
    { txt = "ocaml.ppx.context"; loc = Location.none },
    Parsetree.PStr [Str.eval (Exp.record fields None)]

  let make ~tool_name () =
    let fields =
      [
        lid "tool_name",    make_string tool_name;
        lid "include_dirs", make_list make_string !Clflags.include_dirs;
        lid "load_path",    make_list make_string !Config.load_path;
        lid "open_modules", make_list make_string !Clflags.open_modules;
        lid "for_package",  make_option make_string !Clflags.for_package;
        lid "debug",        make_bool !Clflags.debug;
        get_cookies ()
      ]
    in
    mk fields

  let get_fields = function
    | PStr [{pstr_desc = Pstr_eval
                 ({ pexp_desc = Pexp_record (fields, None) }, [])}] ->
        fields
    | _ ->
        raise_errorf "Internal error: invalid [@@@ocaml.ppx.context] syntax"

  let restore fields =
    let field name payload =
      let rec get_string = function
        | { pexp_desc = Pexp_constant (Pconst_string (str, None)) } -> str
        | _ ->
            raise_errorf
              "Internal error: invalid [@@@ocaml.ppx.context { %s }] string syntax"
              name
      and get_bool pexp =
        match pexp with
        | {pexp_desc = Pexp_construct ({txt = Longident.Lident "true"}, None)} ->
            true
        | {pexp_desc = Pexp_construct ({txt = Longident.Lident "false"}, None)} ->
            false
        | _ ->
            raise_errorf
              "Internal error: invalid [@@@ocaml.ppx.context { %s }] bool syntax"
              name
      and get_list elem = function
        | {pexp_desc =
             Pexp_construct ({txt = Longident.Lident "::"},
                             Some {pexp_desc = Pexp_tuple [exp; rest]}) } ->
            elem exp :: get_list elem rest
        | {pexp_desc =
             Pexp_construct ({txt = Longident.Lident "[]"}, None)} ->
            []
        | _ ->
            raise_errorf
              "Internal error: invalid [@@@ocaml.ppx.context { %s }] list syntax"
              name
      and get_pair f1 f2 = function
        | {pexp_desc = Pexp_tuple [e1; e2]} ->
            (f1 e1, f2 e2)
        | _ ->
            raise_errorf
              "Internal error: invalid [@@@ocaml.ppx.context { %s }] pair syntax"
              name
      and get_option elem = function
        | { pexp_desc =
              Pexp_construct ({ txt = Longident.Lident "Some" }, Some exp) } ->
            Some (elem exp)
        | { pexp_desc =
              Pexp_construct ({ txt = Longident.Lident "None" }, None) } ->
            None
        | _ ->
            raise_errorf
              "Internal error: invalid [@@@ocaml.ppx.context { %s }] option syntax"
              name
      in
      match name with
      | "tool_name" ->
          tool_name_ref := get_string payload
      | "include_dirs" ->
          Clflags.include_dirs := get_list get_string payload
      | "load_path" ->
          Config.load_path := get_list get_string payload
      | "open_modules" ->
          Clflags.open_modules := get_list get_string payload
      | "for_package" ->
          Clflags.for_package := get_option get_string payload
      | "debug" ->
          Clflags.debug := get_bool payload
      | "cookies" ->
          let l = get_list (get_pair get_string (fun x -> x)) payload in
          cookies :=
            List.fold_left
              (fun s (k, v) -> StringMap.add k v s) StringMap.empty
              l
      | _ ->
          ()
    in
    List.iter (function ({txt=Lident name}, x) -> field name x | _ -> ()) fields

  let update_cookies fields =
    let fields =
      List.filter
        (function ({txt=Lident "cookies"}, _) -> false | _ -> true)
        fields
    in
    fields @ [get_cookies ()]

