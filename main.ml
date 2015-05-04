open Parsetree
open Ast_mapper
module H = Ast_helper       
module Loc = Location
module Lid = Longident	       

type 'a loc = 'a Loc.loc

let ppf = Format.err_formatter
	    
type t = { cons: string; nil: string}

(* Subtree builder abstracting over pattern/expr subtree *)	   
type ('desc,'ty) submk = {
    mk : loc:Loc.t -> 'desc -> 'ty;
    tuple: 'ty list -> 'desc;
    construct: Lid.t loc -> 'ty option -> 'desc; 
    destruct: 'ty -> ('ty * 'ty) option;
    ghost_loc : 'ty -> Loc.t;
    mapper: mapper -> 'ty -> 'ty;
    parse : (Lexing.lexbuf->Parser.token) -> Lexing.lexbuf -> 'ty
  }

(* Correct locations when reconstructing subtree for list litterals *)
let relocalize ref_loc loc =
  let open Loc in
  let ref = ref_loc.loc_start in
  let repos rel =
    Lexing.{
	ref with
	pos_lnum = ref.pos_lnum + rel.pos_lnum - 1;
	pos_cnum = ref.pos_cnum + rel.pos_cnum - 1 (* -1 for the ghost "[" *) 
    } in
  { loc_ghost = loc.loc_ghost;
    loc_start = repos loc.loc_start;
    loc_end = repos loc.loc_end
  }
    
let mk submk {cons;_} inner_loc loc ~hd ~tail =
  let args =  submk.mk ~loc @@ submk.tuple [hd; tail] in
  submk.mk ~loc @@
    submk.construct Loc.{ txt=Lid.Lident cons; loc=inner_loc } (Some args)

let mk_nil submk {nil;_} nil_loc =
   let loc = Loc.{ nil_loc with loc_ghost = true } in
   let nil = Loc.{ txt = Lid.Lident nil; loc } in
   submk.mk ~loc @@ submk.construct nil None
	   
let rec mk_list reloc submk term kind nil_loc mapper expr=
  match submk.destruct expr with
  | None -> mk_nil submk kind nil_loc	 		    
  | Some(e1, el) ->
     let hd = submk.mapper mapper e1 in
     match submk.destruct el, term with
     | Some _, _ | _, false -> 
      let tail = mk_list reloc submk term kind nil_loc mapper el
      and loc = reloc @@ submk.ghost_loc hd in
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

(* Expression sequence destructuring *)
let seq_destruct expr=
      match expr.pexp_desc with
      | Pexp_sequence( el, l ) -> Some (el,l)
      | Pexp_construct( {Loc.txt = Lid.Lident "!ll_[]"; loc }, None) -> None
      | exp -> let nowhere = Loc.none in  (*warning: we forge an invalid identifiant to indicate the futur end of the expression sequence *) 
	       Some (expr,
		     { pexp_desc = Pexp_construct ({Loc.txt = Lid.Lident "!ll_[]"; loc=nowhere }, None);
		       pexp_loc = nowhere;
		       pexp_attributes=[]
		     } )
	     

	     
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
	     

	    
(* Check if a quoted string ends with a ".." token *)
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
		     
let env =
  Env.empty
  |+> ( "ll",  { cons="Cons"; nil="Nil" })
  |> ref

(* Imported from Syntaxerr.ml with location information correction *)       
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
			     
let listify kind term constr ref_loc = mk_list (relocalize ref_loc) kind term constr Loc.{ ref_loc with loc_start = ref_loc.loc_end }  
			    
let quoted_string kind mapper super loc = function
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
			   Loc.error ~loc "Error parsing listlike literal"
			 )
	 in
	 let new_mapper =
	   { mapper with location = (fun mapper loc' ->
				     relocalize loc loc' ) } in 
	 listify kind term constr loc new_mapper seq_expr
     else super
  | x -> super
	   

let extract_cstring = function
  | {pexp_desc = Pexp_constant (Asttypes.Const_string(s,_) ); _ } -> Some s
  | _ -> None

	   
let ( **? ) opt1 opt2 = match opt1,opt2 with
  | Some x, Some y -> Some ( x,y )
  | _ -> None

let ll_register l =
  let n = List.length l in
  let args = Array.make 3 "" in
  let free = Array.make 3 true in
  let mark i x = args.(i)<- x; free.(i) <- false in
  let fold l = function
    | "name", x ->  mark 0 x; l 
    | "cons", x  -> mark 1 x; l
    | "nil", x -> mark 2 x; l
    | "", x -> x::l
    | _ -> assert false in
  let nameless_args = List.fold_left fold [] l in
  let rec assign i name =
    if free.(i) then (mark i name; i - 1) else assign (i-1) name in
  match n with
  | 3 -> 
     let _ = List.fold_left assign 2 nameless_args in
     let name, cons , nil = args.(0), args.(1), args.(2) in
     env := !env |+> (name, {cons;nil})
  | _ -> ()
	   
let ll_unregister  = function
  | [ label, name ] -> env:= Env.remove name !env
  | l -> () 

let (>>?) x f = match x with
  | None -> ()
  | Some x -> f x

let rec map_for_all f = function
  | [] -> Some []
  | a::q -> match f a with
	    | None -> None
	    | Some x -> match map_for_all f q with
			| Some l -> Some (x::l)
			| None -> None

let extract_fun = function
  | "register" -> ll_register
  | "unregister" -> ll_unregister
  | _ -> fun l -> ()

let ( |>? ) x f =
  match x with None -> None | Some x -> Some (f x)				     
		    
(* register literal alias *) 		    
let extension_iter =
  let extract_name (e1,n1) = extract_cstring n1 |>? fun n -> (e1,n) in
  let extract_args = map_for_all extract_name in
  function
  | {pstr_desc = Pstr_eval(
      {pexp_desc = Pexp_apply (
		       { pexp_desc =
			   Pexp_ident {Loc.txt=Lid.Lident name ; loc}; _ },
		       args 
		     ); _ },
      _); _  } -> extract_args args >>? extract_fun name 
  | _ -> ()

let extension_payload super expr =
  match expr.pexp_desc with
  | Pexp_extension( {Loc.txt="listlike"; _ }, PStr l ) ->
     let () = List.iter extension_iter l in
     None 
  | _ -> Some ( super () )
	   
let structure_item mapper item =
  let default () = default_mapper.structure_item mapper item in
  match item.pstr_desc with 
  | Pstr_eval (expr,_)  -> extension_payload default expr
  | item -> Some (default () )

let value_binding mapper {pvb_pat; pvb_expr; pvb_attributes; pvb_loc} =
  let pvb_pat = mapper.pat mapper pvb_pat in
  let pvb_expr = mapper.expr mapper pvb_expr in
  let pvb_loc = mapper.location mapper pvb_loc in
  let pvb_attributes = mapper.attributes mapper pvb_attributes in
  {
    pvb_pat;
    pvb_expr;
    pvb_loc;
    pvb_attributes
  } 
         		 
				       
let structure_map mapper s =
  let cons_opt l item =
    match structure_item mapper item with
    | Some x -> x::l
    | None -> l in 
 List.rev @@  List.fold_left cons_opt [] s


	
let const_expr mapper f = function
  | { pexp_desc = Pexp_constant const; pexp_loc } as super ->
     f expr mapper super pexp_loc const
  | x -> default_mapper.expr mapper x

let const_patt mapper f = function
  | { ppat_desc = Ppat_constant const; ppat_loc } as super ->
     f patt mapper super ppat_loc const
  | x ->default_mapper.pat mapper x			     

let unit loc = Pexp_construct ( Loc.{txt= Lid.Lident "()";loc}, None) 
		
let expression_map mapper exp =
  match exp.pexp_desc with
  | Pexp_constant const -> quoted_string expr mapper exp exp.pexp_loc const
  | Pexp_extension ({Loc.txt="listlike"; _ }, PStr l) ->
     List.iter extension_iter l;
     { exp with pexp_desc = unit exp.pexp_loc }
  | Pexp_sequence (e1,e2) ->
     let e1' = mapper.expr mapper e1 in
     { exp with pexp_desc = Pexp_sequence (e1', mapper.expr mapper e2 ) } 
  | _ -> default_mapper.expr mapper exp

    
let pattern_map mapper = const_patt mapper @@ quoted_string
							       
let listlike_mapper argv = { 
  default_mapper with
    expr = expression_map;
    pat= pattern_map;
    structure = structure_map;
    value_binding
  }

let () = register "listlike" listlike_mapper
