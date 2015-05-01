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
    destruct: 'ty -> 'ty * 'ty option;
    mapper: mapper -> 'ty -> 'ty;
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
  | e1, Some el ->
      let hd = submk.mapper mapper e1 in
      let tail = mk_list submk kind nil_loc mapper el
      and loc = Loc.{ hd.pexp_loc with loc_ghost = true} in
      mk submk kind loc loc ~hd ~tail
  |  desc ->
      let nil = mk_nil submk kind nil_loc in
      let expr = mapper.expr mapper expr in
      let loc = Loc.{ expr.pexp_loc with loc_ghost = true} in
      mk submk kind loc loc ~hd:expr ~tail:nil  
	 		    

let expr = {
    mk =(fun ~loc expr ->  H.Exp.mk ~loc expr);
    tuple = (fun l -> Pexp_tuple l);
    construct = (fun loc args -> Pexp_construct(loc,args) );
    destruct =(
      fun expr ->
      match expr.pexp_desc with
      | Pexp_construct( {Loc.txt=Lid.Lident "::" ; loc }, Some {pexp_desc=Pexp_tuple [el;l];_} ) ->
	 (el, Some l)
      | Pexp_construct( {Loc.txt=Lid.Lident "[]";loc}, None) ->
	 expr, None
      | _ -> assert false );
    mapper = ( fun mapper expr -> mapper.expr mapper expr);
  }
	 
			   
module Exp = struct        
    let mk {cons;_} inner_loc loc ~hd ~tail =
      let args =  H.Exp.mk ~loc (Pexp_tuple [hd; tail]) in
      H.Exp.mk ~loc (Pexp_construct(Loc.mkloc (Lid.Lident cons) inner_loc, Some args))
	       
let mk_nil {nil;_} nil_loc =
   let loc = Loc.{ nil_loc with loc_ghost = true } in
   let nil = Loc.{ txt = Lid.Lident nil; loc } in
   H.Exp.mk ~loc (Pexp_construct (nil, None))
	   
let rec mk_list kind nil_loc mapper expr=
  match expr.pexp_desc with
  | Pexp_sequence(e1, el) ->
      let hd = mapper.expr mapper e1 in
      let tail = mk_list kind nil_loc mapper el
      and loc = Loc.{ hd.pexp_loc with loc_ghost = true} in
      mk kind loc loc ~hd ~tail
  |  desc ->
      let nil = mk_nil kind nil_loc in
      let expr = mapper.expr mapper expr in
      let loc = Loc.{ expr.pexp_loc with loc_ghost = true} in
      mk kind loc loc ~hd:expr ~tail:nil  
	 
end

module Pat = struct
	       
let mk {cons;_} inner_loc args loc =
  H.Pat.mk ~loc (Ppat_construct(Loc.mkloc (Lid.Lident cons) inner_loc, Some args))

let rec mklist kind nil_loc = function
    [] ->
      let loc = Loc.{ nil_loc with loc_ghost = true } in
      let nil = Loc.{ txt = Lid.Lident kind.nil; loc } in
      H.Pat.mk ~loc (Ppat_construct (nil, None))
  | p1 :: pl ->
      let pat_pl = mklist kind nil_loc pl
      and loc = Loc.{ p1.ppat_loc with  loc_ghost = true} in
      let arg = H.Pat.mk ~loc (Ppat_tuple [p1; pat_pl]) in
      mk kind Loc.{loc with loc_ghost = true} arg loc
end

let default = { cons="Cons"; nil="Nil"}	       

module Map = struct		
    let const mapper f = function
      | { pexp_desc = Pexp_constant const; _ } as exp -> f mapper exp const
      | x -> x
	       
    let string listify mapper exp = function
      | Asttypes.Const_string(s, Some "listlike") -> 
	 let seq_expr = Parser.parse_expression Lexer.token @@ Lexing.from_string s in
	 listify mapper seq_expr
      | x -> exp 
  end
	       
let listify seq = mk_list expr default (Loc.none) seq  
		       
let expression_map mapper = Map.(const mapper  @@ string listify)

let listlike_mapper argv = { 
  default_mapper with
  expr = expression_map 
}

let () = register "listlike" listlike_mapper
