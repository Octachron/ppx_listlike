open Parsetree
module H = Ast_helper
module Loc = Location
open Env_mapper
type 'a loc = 'a Loc.loc
    
type lid = Longident.t =
  | Lident of string
  | Ldot of  lid * string
  | Lapply of lid * lid


let fatal_error loc str = raise Location.( Error( error ~loc str) )
let pp = Format.sprintf
let expected loc str =
  fatal_error loc @@ pp "Ppx_listlike: %s expected" str
let ghost loc_a = Loc.{ loc_a with loc_ghost = true }
                    
module Lid = struct
  let from_string loc s =
    let n = String.length s in
    let rec split s no_dot pos ende = match s.[pos] with
      | '.' ->
        if no_dot then
          fatal_error loc @@ pp "Ppx_listlike: invalid constructor name"
        else
          Ldot(split s true (pos-1) (pos-1),  String.sub s (pos+1) (ende-pos) )
      | _ when pos =0 -> Lident (String.sub s 0 (ende+1))
      | _ -> split s false (pos-1) ende in
    split s true (n-1) (n-1)
end

let fold_map (|+>) map start l =
  List.fold_left
    (fun acc x -> acc |+> map x )
    start
    l
    
type kind = List | Array_indices | Bigarray_indices | String_indices
            
module Constructor = struct
  type t = { kind:kind; cons: lid; nil: lid}
  let default = "ll", { kind=List; cons=Lident "Cons"; nil=Lident "Nil" }
  let std = "stdl", { kind=List; cons=Lident "::"; nil=Lident "[]" }
end


let nil c = c.Constructor.nil
let cons c = c.Constructor.cons
               
module Defs = struct
  include Map.Make(
    struct
      type t = string
      let compare (x:string) y = compare x y
    end)
  type st = Constructor.t t
  let (|+>) env (key,value) = add key value env
end

module Status = struct
  include Map.Make(
    struct
      type t=kind
      let compare (x:kind) y = compare x y
    end)
      
  type st = Constructor.t t
    let (|+>) env constr =
      let open Constructor in add constr.kind constr env
    let find_opt kind status =
      try Some (find kind status) with
      | Not_found -> None
        
end

module Env = struct
  type t = {
    defs: Defs.st;
    status: Status.st
  }
  
  let empty = { defs = Defs.empty; status=Status.empty }
  let define def env =
    { env with defs = Defs.( env.defs |+> def ) }
  let activate cons env =
    { env with status = Status.( env.status |+> cons )}
    
  
  let default =
    empty
    |> define Constructor.default
    |> define Constructor.std
end

module Indices = struct
  
  let map_2 f (a,b) = a, f b
                        
  let map special f g l =
    let rec map special f g l =
      if special <= 0 then List.map (map_2 f) l else
        match l with
        | a::q -> (map_2 g a)::(map (special - 1) f g q)
        | [] -> [] in
    match l with
    | a::q -> (map_2 f a)::(map special f g q)
    | [] -> []
            
  let array_map g e = match e.pexp_desc with
    | Pexp_array l -> { e with pexp_desc = Pexp_array (List.map g l) }
    | _ -> e
      
  let map_generic f g l =
    map 1 f (array_map g) l
      
  
  let identify_lid lid =
    match lid with
    | Lident (".()"|".()<-")
    | Ldot( Lident "Array", ("get"|"unsafe_get"|"set"|"unsafe_set") )
      -> Some (Array_indices, map 1)
    | Lident (".[]"|".[]<-")
    | Ldot( Lident "String", ("get"|"unsafe_get"|"unsafe_set"|"set") )
      ->  Some (String_indices, map 1)
    | Lident (".{}"|".{}<-")
    | Ldot( Ldot ( Lident "Bigarray", "Array1" ) ,
            ("get"|"unsafe_get"|"set"|"unsafe_set") ) ->
      Some (Bigarray_indices, map 1)
    | Lident (".{,}"|".{,}<-")
    | Ldot( Ldot ( Lident "Bigarray", "Array2" ) ,
            ("get"|"unsafe_get"|"set"|"unsafe_set") ) ->
      Some (Bigarray_indices, map 2)
    | Lident (".{,,}"|".{,,}<-")
    | Ldot( Ldot ( Lident "Bigarray", "Array3" ) ,
            ("get"|"unsafe_get"|"set"|"unsafe_set") ) ->
      Some (Bigarray_indices, map 3)
    | Lident (".{,..,}"|".{,..,}<-")
    | Ldot( Ldot ( Lident "Bigarray", "Genarray" ) ,
            ("get"|"unsafe_get"|"set"|"unsafe_set") ) ->
      Some (Bigarray_indices, map_generic )
    | _ -> None
      
  
  let identify exp =
    match exp.pexp_desc with
    | Pexp_ident lid -> identify_lid lid.Loc.txt
    | _ -> None
      
end

module Opt = struct

  let (>>?) x f = match x with
    | None -> ()
    | Some x -> f x

  let ( >>=? ) x f =
    match x with None -> None | Some x -> f x
                                            
  let rec map_for_all f = function
    | [] -> Some []
    | a::q -> match f a with
      | None -> None
      | Some x -> match map_for_all f q with
        | Some l -> Some (x::l)
        | None -> None
          
  let ( |>? ) x f =
    match x with None -> None | Some x -> Some (f x)
                                            
  let may f param x = match param with
    | Some p -> f p x
    | None -> x
      
  let (><?) opt default = match opt with
    | Some x -> x
    | None -> default
      
end
open Opt
    

let replace_constr cons lid=
  let open Loc in
  let open Lid in
  let open Constructor in
  match lid.txt with
  | Lident "::" ->  { lid with txt = cons.cons }
  | Lident "[]" -> { lid with txt = cons.nil }
  | _ -> lid
    
module Interpreter = struct
  
  type microtype = Kind of kind | Constructor of lid
                     
  let var pat = match pat.ppat_desc with
    | Ppat_var {Loc.txt;loc} -> txt
    | _ -> expected pat.ppat_loc "pattern variable"
             
  let const_string e= match e.pexp_desc with
    | Pexp_constant ( Asttypes.Const_string(s, _ ) ) -> s
    | _ -> expected e.pexp_loc "string litteral"
             
  let constructor e = match e.pexp_desc with
    | Pexp_construct(llid,None) -> llid.Loc.txt
    | _ -> expected e.pexp_loc "constructor"
             
  let kind loc = function
    | Lident x -> (
        match x with
        | "List"-> List
    | "Array_indices" -> Array_indices
    | "String_indices" -> String_indices
    | "Bigarray_indices" -> Bigarray_indices
    | _ -> expected loc "constructor kind \
                         (i.e. List|Array_indices|String_indices|Bigarray_indices)"
      )
    | _ -> expected loc "long identifier"
             
  let field (llid,e) =
    let open Lid in
    let txt = llid.Loc.txt in
    let loc = llid.Loc.loc in
    match txt with
    | Lident "kind" -> "kind" , Kind( kind loc @@ constructor e )
    | Lident ("cons" as s) | Lident ("nil" as s)  ->
      s, Constructor(Lid.from_string loc @@ const_string e)
  | _ -> fatal_error llid.Loc.loc @@
    pp "Ppx_listlike: Unknown field name in constructor description"
      
  let destruct_kind = function
    | Kind k -> k
    |  _ -> assert false
      
  let destruct_cons = function
    | Constructor c -> c
    | _ -> assert false
      
let reconstruct named =
  let find x = Defs.find x named in
  let find_cons x = destruct_cons @@ find x in
  let kind, cons, nil =
    destruct_kind @@ find "kind",
    find_cons "cons",
    find_cons "nil" in
  Constructor.{ kind; cons; nil }
    
let record e = match e.pexp_desc with
  | Pexp_record (l, None ) ->
    let open Defs in
    let named = fold_map (|+>) field empty l in
    reconstruct named
  | _ -> expected e.pexp_loc "record"
           

let binding b =
  var b.pvb_pat,
  record b.pvb_expr
    
end

module Expr_seq = struct
  
  let mk_nil constr nil_loc =
    let loc = ghost nil_loc in
    let lid =Loc.{txt = nil constr ; loc } in
    H.Exp.construct ~loc lid None
      
  let mk_cons constr loc e1 e2 =
    let loc = ghost loc in
    let constr = Loc.{txt = cons constr; loc} in
    let tuple = H.Exp.tuple ~loc [e1;e2] in
    H.Exp.construct ~loc constr (Some tuple)
      
  let rec mk_list cons mapper env exp=
    match exp.pexp_desc with
    | Pexp_sequence (e1,e2 ) ->
      let e1 = rm_env mapper.expr mapper env e1 in
      mk_cons cons exp.pexp_loc e1 @@  mk_list cons mapper env e2
    | _ ->
      let exp = rm_env mapper.expr mapper env exp in
      let nil = mk_nil cons Loc.none in
      mk_cons cons exp.pexp_loc exp nil
end


module Expr = struct
    let ppx_interpreter mapper env expr =
      let open Defs in
      match expr.pexp_desc with
      | Pexp_let (Asttypes.Nonrecursive, bindings, e ) ->
        let defs =
          fold_map (|+>) Interpreter.binding Env.(env.defs) bindings in
        rm_env mapper.expr mapper Env.{ env with defs } e
      | _ -> assert false

    let extract  = function
      | PStr [] -> (* [%ext] is replaced by [] *)
        Some (Expr_seq.mk_nil (snd Constructor.std) Loc.none)
      | PStr [ {pstr_desc = Pstr_eval (expr, _) ; _ } ] -> Some expr
      | _ -> None
        
    let extension mapper env super (name, payload) =
      let open Env in
      let open Loc in
      match name.txt, extract payload with
      | "ppx_listlike", Some expr -> ppx_interpreter mapper env expr
      | s, Some expr -> (
          try
            let constr = Defs.find s env.defs in
            Expr_seq.mk_list constr mapper env expr
          with Not_found -> super
        )
      | _ -> super
end


let expr mapper env expr =
  let open Status in
  let open Env in
  match expr.pexp_desc with
  | Pexp_construct (lid, expr_opt) ->
    let lid =  Opt.may replace_constr (find_opt List env.status) lid
    and expr_opt = expr_opt |>? rm_env mapper.expr mapper env in
    env, { expr with pexp_desc = Pexp_construct( lid, expr_opt) }
  | Pexp_apply (f, args) ->
    let f = rm_env mapper.expr mapper env f in
    env,
    Indices.identify f
    >>=? (fun (kind,arg_map) -> Status.find_opt kind Env.(env.status)
    |>? ( fun cons ->
        H.Exp.apply ~loc:expr.pexp_loc f @@
        arg_map
          (rm_env mapper.expr mapper env )
          (Expr_seq.mk_list cons mapper env)
          args
      ) 
    )
    ><? rm_env Env_mapper.identity.expr mapper env expr
  | Pexp_extension ext -> env, Expr.extension mapper env expr ext
  | _ -> Env_mapper.identity.expr mapper env expr
           
module Pat = struct
  let ppx_interpreter mapper env pat =
    rm_env mapper.pat mapper env pat
      
  let extract = function
    | PPat (pat,None) -> Some (pat)
    | _ -> None
      
  let extension mapper env super (name, payload) =
    let open Env in
    let open Loc in
    match name.txt, extract payload with
    | "ppx_listlike", Some pat -> ppx_interpreter mapper env pat
    | s, Some (pat) -> (
        try
          let constr = Defs.find s env.defs in
          let env = activate constr env in
    rm_env mapper.pat mapper env pat
        with Not_found -> super
      )
    | _ -> super
end


let pat mapper env pat =
  let open Status in
  let open Env in
  match pat.ppat_desc with
  | Ppat_construct (lid, pat_opt) ->
     let lid =  Opt.may replace_constr (find_opt List env.status) lid
     and pat_opt = pat_opt |>? rm_env mapper.pat mapper env in
     env, { pat with ppat_desc = Ppat_construct( lid, pat_opt) }
  | Ppat_extension ext -> env, Pat.extension mapper env pat ext
  | _ -> Env_mapper.identity.pat mapper env pat
           

module Case = struct
  let ppx_interpreter mapper env case =
    rm_env mapper.case mapper env case
      
  let extract = function
    | PPat (pat,guard) -> Some (pat,guard)
    | _ -> None
      
  let extension mapper env super (name, payload) =
    let open Env in
    let open Loc in
    match name.txt, extract payload with
    | "ppx_listlike", Some (pc_lhs,pc_guard) ->
      let case = {super with pc_lhs ;pc_guard} in
      ppx_interpreter mapper env case
    | s, Some (pat,guard) -> (
        try
          let constr = Defs.find s env.defs in
          let pc_rhs = rm_env mapper.expr mapper env super.pc_rhs in
          let env = activate constr env in
          let pc_lhs = rm_env mapper.pat mapper env pat in
          let pc_guard = guard |>? rm_env mapper.expr mapper env in
          Some {pc_lhs; pc_guard; pc_rhs}
        with Not_found -> Some super
      )
    | _ -> Some super
end


let case mapper env case =
  let open Status in
  let open Env in
  match case.pc_lhs.ppat_desc with
  | Ppat_extension ext -> env, Case.extension mapper env case ext
  | _ -> Env_mapper.identity.case mapper env case
           


module Str = struct
  
  let fold_binding defs item =
    match item.pstr_desc with
    | Pstr_value(Asttypes.Nonrecursive, bindings) ->
      fold_map Defs.(|+>) Interpreter.binding defs bindings
    | _ -> assert false
      
  let ppx_interpreter mapper env str =
    let open Defs in
    let defs =
      List.fold_left fold_binding Env.(env.defs) str in
    Env.{env with defs}, []
                         
  
  let extract  = function
    | PStr str -> Some str
    | _ -> None
      
  let extension mapper env super (name, payload) =
    let open Env in
    let open Loc in
      match name.txt, extract payload with
        | "ppx_listlike", Some str -> ppx_interpreter mapper env str
        | s, Some str -> (
            try
              let constr = Defs.find s env.defs in
              mapper.structure mapper (activate constr env) str
            with Not_found -> env, [super]
          )
        | _ -> env, [super]
end

let structure mapper env =
  let open Status in
  let open Env in
  function
  | [] -> env, []
  | item::q ->
    let q env = mapper.structure mapper env q in
    match item.pstr_desc with
    | Pstr_extension (ext,attributes) ->
      let env', str = Str.extension mapper env item ext in
      let env = {env with defs = env'.defs } in
      let env, q = q env in
      env, str @ q
    | _ ->
      let env', q = q env in
      env',
      cons_opt
        (rm_env Env_mapper.identity.structure_item mapper env item)
        q
        
let listlike_mapper argv =
  to_transform Env.default
    { identity  with
      expr;
      pat;
      structure;
      case
    }

let () = Ppx_register.register "listlike" listlike_mapper
