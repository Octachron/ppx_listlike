open Parsetree
module H = Ast_helper       
module Loc = Location
module Lid = Longident	       
open Env_mapper
type 'a loc = 'a Loc.loc
		 

let ppf = Format.err_formatter

type kind = List | Array | String | Bigarray
	    
module Cons = struct	    
    type t = { kind:kind; cons: string; nil: string}
    let default = "ll", { kind=List; cons="Cons"; nil="Nil" }
  end
		
module Defs =
  struct 
    include Map.Make(
		struct
		  type t = string
		  let compare (x:string) y = compare x y
		end)
    let (|+>) env (key,value) = add key value env 		  
  end

module Status = struct
    include Map.Make(
		struct
		  type t=kind
		  let compare (x:kind) y = compare x y
		end)

    type st = Cons.t t 
    let (|+>) env constr =
      let open Cons in add constr.kind constr env
    let find_opt kind status =
      try Some (find kind status) with
      | Not_found -> None 

end
		      
module Env = struct
    type t = {
	defs: Cons.t Defs.t;
	status: Status.st
      }
	       
	   
    let empty = { defs = Defs.empty; status=Status.empty }	     
    let define ~env ~def =
      { env with defs = Defs.( env.defs |+> def ) }
    let activate ~env ~cons =
      { env with status = Status.( env.status |+> cons )}   
				      
		       
    let default = define empty Cons.default 
  end
(*
let array_env =
  Indices.(
    empty
    |+> (Array, {cons="Cons_array"; nil= "Nil_array"})
    |+> (String, {cons="Cons_string"; nil= "Nil_string"})
    |+> (Bigarray, {cons="Cons_bigarray"; nil= "Nil_bigarray"})
  )

	       
let identify_array_kind lid =
  let open Lid in
  match lid with
  | Lident (".()" | ".()<-")
  | Ldot( Lident "Array", ("get"|"set"|"unsafe_set"|"unsafe_get") ) ->
     Some Array
  | Lident (".[]" | ".[]<-")
  | Ldot(Lident "String", ("get"|"set"|"unsafe_set"|"unsafe_get") ) ->
     Some String
  | Lident (".{}" | ".{}<-")
  | Ldot(
	Ldot ( Lident "Bigarray", "Array1" ),
	("get"|"set"|"unsafe_set"|"unsafe_get")
      )  ->
     Some Bigarray
  | _ -> None 
 *)

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
  let open Cons in
  match lid.txt with
  | Lident "::" ->  { lid with txt = Lident cons.cons }
  | Lident "[]" -> { lid with txt = Lident cons.nil }
  | _ -> lid

module Expr = struct
    let ppx_interpreter mapper env expr =
      rm_env mapper.expr mapper env expr	   
	     
	     
    let extract  = function
      | PStr [ {pstr_desc = Pstr_eval (expr, _) ; _ } ] -> Some expr
      | _ -> None
	       
    let extension mapper env super (name, payload) =
      let open Env in
      let open Loc in
      match name.txt, extract payload with
      | "ppx_listlike", Some expr -> ppx_interpreter mapper env expr
      | s, Some expr -> (
	try
	  let cons = Defs.find s env.defs in
	  rm_env mapper.expr mapper (activate env cons) expr 
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
	  let cons = Defs.find s env.defs in
	  let env = activate env cons in
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
	  let cons = Defs.find s env.defs in
	  let env = activate env cons in
	  let pc_lhs = rm_env mapper.pat mapper env pat in
	  let pc_guard = guard |>? rm_env mapper.expr mapper env in
	  Some {super with pc_lhs; pc_guard }
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
    let ppx_interpreter mapper env str =
      mapper.structure mapper env str	   
	     
	     
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
	  let cons = Defs.find s env.defs in
	  mapper.structure mapper (activate env cons) str 
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
				 

	  
(*		      
let uniformize_args kind mapper loc  =
  function
  | arg1::(lbl,seq)::q ->
     let constr = Indices.find kind array_env in
     arg1::(
       lbl,
       mk_list
	 ( fun loc -> loc)
	 { expr with destruct = seq_destruct }
	 false
	 constr
	 Loc.{ loc with loc_start = loc.loc_end }
	 mapper
	 seq
     )::q
  | args -> args
 *)  
(*		
let expression_map mapper exp =
  let default () = default_mapper.expr mapper exp in
  match exp.pexp_desc with
  | Pexp_constant const -> quoted_string expr mapper exp exp.pexp_loc const
  | Pexp_extension ({Loc.txt="listlike"; _ }, PStr l) ->
     List.iter extension_iter l;
     { exp with pexp_desc = unit exp.pexp_loc }
  | Pexp_sequence (e1,e2) ->
     let e1' = mapper.expr mapper e1 in
     { exp with pexp_desc = Pexp_sequence (e1', mapper.expr mapper e2 ) }
  | Pexp_apply (f, args ) ->
     begin
       match f.pexp_desc with
       | Pexp_ident ident ->
	  ( match identify_array_kind ident.Loc.txt with
	    | Some kind ->
	       let loc = exp.pexp_loc in
	       { f with pexp_desc =
			  Pexp_apply( f, uniformize_args kind mapper loc args )
	       }
	    | None -> default ()
	  )
      | _ -> default ()
    end 
  | _ -> default ()
 *)
    			       
let listlike_mapper argv =
  to_transform Env.default
	       { 
		 identity  with
		 expr;
		 pat;
		 structure;
		 case
	       }

let () = Ppx_register.register "listlike" listlike_mapper
