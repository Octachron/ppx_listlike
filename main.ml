open Parsetree
open Ast_mapper
module H = Ast_helper       
module Loc = Location
module Lid = Longident	       

type 'a loc = 'a Loc.loc
	       
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
	   
let rec mk_list submk kind nil_loc mapper expr=
  match submk.destruct expr with
  | Some(e1, el) ->
      let hd = submk.mapper mapper e1 in
      let tail = mk_list submk kind nil_loc mapper el
      and loc = submk.ghost_loc hd in
      mk submk kind loc loc ~hd ~tail
  | None -> mk_nil submk kind nil_loc	 		    

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
  | { pexp_desc = Pexp_constant const; _ } as exp -> f mapper exp const
  | x -> x

let const_patt mapper f = function
  | { ppat_desc = Ppat_constant const; _ } as patt -> f mapper patt const
  | x -> x
	    

	   
let string kind listify mapper exp = function
  | Asttypes.Const_string(s, Some "listlike") -> 
     let seq_expr = kind.parse Lexer.token @@
		      Lexing.from_string @@ "["^s^"]" in
     listify kind mapper seq_expr
  | x -> exp 
		
	       
let listify kind seq = mk_list kind default (Loc.none) seq  
		       
let expression_map mapper = const_expr mapper  @@ string expr @@ listify
let pattern_map mapper = const_patt mapper @@ string patt @@ listify

let listlike_mapper argv = { 
  default_mapper with
    expr = expression_map;
    pat= pattern_map
}

let () = register "listlike" listlike_mapper
