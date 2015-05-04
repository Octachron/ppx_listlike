open Parsetree
open Ast_mapper
module H = Ast_helper       
module Loc = Location
module Lid = Longident	       

type 'a loc = 'a Loc.loc

let ppf = Format.err_formatter
		 
type t = { cons: string; nil: string}

type ('desc,'ty) submk = {
    mk : loc:Loc.t -> 'desc -> 'ty;
    tuple: 'ty list -> 'desc;
    construct: Lid.t loc -> 'ty option -> 'desc; 
    destruct: 'ty -> ('ty * 'ty) option;
    ghost_loc : 'ty -> Loc.t;
    mapper: mapper -> 'ty -> 'ty;
    parse : (Lexing.lexbuf->Parser.token) -> Lexing.lexbuf -> 'ty
  }

let mk submk {cons;_} inner_loc loc ~hd ~tail =
  let args =  submk.mk ~loc @@ submk.tuple [hd; tail] in
  submk.mk ~loc @@
    submk.construct Loc.{ txt=Lid.Lident cons; loc=inner_loc } (Some args)

let mk_nil submk {nil;_} nil_loc =
   let loc = Loc.{ nil_loc with loc_ghost = true } in
   let nil = Loc.{ txt = Lid.Lident nil; loc } in
   submk.mk ~loc @@ submk.construct nil None
	   
let rec mk_list submk term kind nil_loc mapper expr=
  match submk.destruct expr with
  | None -> mk_nil submk kind nil_loc	 		    
  | Some(e1, el) ->
     let hd = submk.mapper mapper e1 in
     match submk.destruct el, term with
     | Some _, _ | _, false -> 
      let tail = mk_list submk term kind nil_loc mapper el
      and loc = submk.ghost_loc hd in
      mk submk kind loc loc ~hd ~tail
     | None, true -> hd

let expr = {
    mk =(fun ~loc expr ->  H.Exp.mk ~loc expr);
    tuple = (fun l -> Pexp_tuple l);
    construct = (fun loc args -> Pexp_construct(loc,args) );
    destruct =(
      fun expr ->
      match expr.pexp_desc with
      | Pexp_construct(
	  {Loc.txt=Lid.Lident "::" ; loc },
	  Some {pexp_desc=Pexp_tuple [el;l];_}
	) -> Some(el, l)
      | Pexp_construct( {Loc.txt=Lid.Lident "[]";loc}, None) ->
	 None
      | _ -> assert false );
    ghost_loc  = (fun expr -> Loc.{ expr.pexp_loc with loc_ghost=true } ); 
    mapper = ( fun mapper expr -> mapper.expr mapper expr);
    parse = Parser.parse_expression;
  }

let patt = {
    mk = (fun ~loc patt -> H.Pat.mk ~loc patt);
    tuple = (fun l -> Ppat_tuple l);
    construct = (fun loc args -> Ppat_construct(loc,args) );
    mapper = (fun mapper patt -> mapper.pat mapper patt); 
    ghost_loc  = (fun pattern -> Loc.{ pattern.ppat_loc with loc_ghost=true } );
    parse = Parser.parse_pattern;
    destruct = (
      fun pattern ->
      match pattern.ppat_desc with
      | Ppat_construct(
	  {Loc.txt=Lid.Lident "::"; loc },
	  Some {ppat_desc=Ppat_tuple [el;l];_}
	) -> Some(el, l)
      | Ppat_construct( {Loc.txt=Lid.Lident "[]"; loc }, None ) -> None
      | _ -> assert false
    );
  }


let default = { cons="Cons"; nil="Nil"}	       
	
let const_expr mapper f = function
  | { pexp_desc = Pexp_constant const; pexp_loc } as super ->
     f expr mapper super pexp_loc const
  | x -> default_mapper.expr mapper x

let const_patt mapper f = function
  | { ppat_desc = Ppat_constant const; ppat_loc } as super ->
     f patt mapper super ppat_loc const
  | x ->default_mapper.pat mapper x
	    

let term_parse s=
  let none = false, s in
  let rec seek k =
    if k<1 then none else
      match s.[k-1],s.[k]  with
      | _, (' '|'\009'|'\012'|'\010'|'\013')  -> seek (k-1)
      | '*',')' -> ignore_comments 1 (k-1)
      | '.','.' -> true, String.sub s 0 (k-1)
      | _ -> none 
  and ignore_comments cl k =
    if cl = 0 then seek k else
    if k<1 then none else
      match s.[k-1],s.[k] with
      | '*',')' -> ignore_comments (cl+1) (k-2)
      | '(','*' -> ignore_comments (cl-1) (k-2)
      | _ -> ignore_comments cl (k-1) in
  seek @@ (String.length s) - 1
	    
module Env = Map.Make(struct type t = string let compare (x:string) y = compare x y end)

let (|+>) env (key,value) = Env.add key value env
let (|?) name env = Env.mem name env				    
		     
let env =  Env.empty |+> ( "ll",  { cons="Cons"; nil="Nil" }) |> ref
				
let to_path s =
  let len = String.length s in
  let rec split path start k =
    if k>=len then (String.sub s start (len-start) :: path ) else
      match s.[k] with
      | '_' -> split (String.sub s start (k-start) :: path) (k+1) (k+1)
      | _ -> split path start (k+1)
  in
  List.rev @@ split [] 0 0

let rec constructors path =
  let buffer = Buffer.create 20 in
  let rec aux = function
    | [] -> Buffer.contents buffer
    | ""::q -> aux q
    | a::q -> List.iter (Buffer.add_string buffer) ["_";a]; aux q in
  let suffix = aux path in
  { cons = "Cons"^suffix; nil = "Nil"^suffix }
								

let relocalize ref_loc loc =
  let open Loc in
  let ref = ref_loc.loc_start in
  let repos rel =
    Lexing.{
	ref with
	pos_lnum = ref.pos_lnum + rel.pos_lnum;
	pos_cnum = ref.pos_cnum + rel.pos_cnum - 1 (* -1 for the ghost "[" *) 
    } in
  { loc_ghost = loc.loc_ghost;
    loc_start = repos loc.loc_start;
    loc_end = repos loc.loc_end
  }
    
let subparser_error loc  =
  let open Syntaxerr in
  let reloc = relocalize loc in
  function
  | Unclosed(opening_loc, opening, closing_loc, closing) ->
      Location.raise_errorf ~loc:(reloc closing_loc)
        ~sub:[
          Location.error ~loc:(reloc opening_loc)
            (Printf.sprintf "Error: This '%s' might be unmatched" opening)
        ]
        ~if_highlight:
          (Printf.sprintf "Syntax error: '%s' expected, \
                           the highlighted '%s' might be unmatched"
             closing opening)
        "Error: Syntax error: '%s' expected" closing

  | Expecting (loc, nonterm) ->
     Location.raise_errorf ~loc:(reloc loc)
			   "Error: Syntax error: %s expected." nonterm
  | Not_expecting (loc, nonterm) ->
     Location.raise_errorf ~loc:(reloc loc)
		     "Error: Syntax error: %s not expected." nonterm
  | Applicative_path loc ->
      Location.raise_errorf ~loc:(reloc loc)
        "Error: Syntax error: applicative paths of the form F(X).t \
         are not supported when the option -no-app-func is set."
  | Variable_in_scope (loc, var) ->
      Location.raise_errorf ~loc:(reloc loc)
        "Error: In this scoped type, variable '%s \
         is reserved for the local type %s."
        var var
  | Other loc ->
      raise @@ Loc.Error (Location.error ~loc:(reloc loc) "Error: Syntax error")
  | Ill_formed_ast (loc, s) ->
      Location.raise_errorf ~loc:(reloc loc) "Error: broken invariant in parsetree: %s" s
			      
 
	   
let string listify kind mapper super loc = function
  | Asttypes.Const_string(s, Some name) ->
     if Env.mem name !env then
       let constr = Env.find name !env in
       let term, s = term_parse s in 
	 let seq_expr =
	   try
	     kind.parse Lexer.token @@ Lexing.from_string @@ "["^s^"]"	
	   with
	   |  Syntaxerr.Error err -> subparser_error loc err
	   | Parsing.Parse_error ->
	      raise @@ Loc.Error(
			   Loc.error ~loc "Error parsing listlike litteral"
			 )
	 in
	 listify kind term constr mapper seq_expr
     else super
  | x -> super
	   
	       
let listify kind term constr = mk_list kind term constr (Loc.none)  

let extract_cstring = function
  | {pexp_desc = Pexp_constant (Asttypes.Const_string(s,_) ); _ } -> Some s
  | _ -> None


	   
let ( **? ) opt1 opt2 = match opt1,opt2 with
  | Some x, Some y -> Some ( x,y )
  | _ -> None

let ll_register (name,(cons,nil)) =
  env := !env |+> (name, {cons;nil})
	   
let extension_iter =
  function
  | {pstr_desc = Pstr_eval(
      {pexp_desc = Pexp_apply (
		       { pexp_desc =
			   Pexp_ident {Loc.txt=Lid.Lident "register"; loc}; _ },
		       [ l1, e1; l2, e2; l3, e3 ]
		     ); _ },
      _); _  } ->
     begin
       let ( ~? ) =  extract_cstring in  
      match ~?e1 **? ~?e2 **? ~?e3 with
      | Some x -> ll_register x
      | None -> ()
     end
  | _ -> ()
	   
let structure_item mapper = function
  | { pstr_desc = Pstr_eval (
      {pexp_desc= Pexp_extension ({Loc.txt="listlike"; _ }, payload); _ },
      att
    ); _ }  as super
    -> begin match payload with
	     | PStr l ->
		let () = List.iter extension_iter l in
		None 
	     | _ -> Some super
     end
  | item -> Some (default_mapper.structure_item mapper item)
				       
let structure_map mapper s =
  let cons_opt l item =
    match structure_item mapper item with
    | Some x -> x::l
    | None -> l in 
 List.rev @@  List.fold_left cons_opt [] s

				       
let expression_map mapper = const_expr mapper  @@ string listify
let pattern_map mapper = const_patt mapper @@ string listify
							       
let listlike_mapper argv = { 
  default_mapper with
    expr = expression_map;
    pat= pattern_map;
    structure = structure_map;
  }

let () = register "listlike" listlike_mapper
