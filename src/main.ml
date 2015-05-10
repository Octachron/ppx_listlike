open Parsetree
module H = Ast_helper       
module Loc = Location
module Lid = Longident	       
open Env_mapper
type 'a loc = 'a Loc.loc
		 
type lid = Lid.t =
      | Lident of string
      | Ldot of  lid * string
      | Lapply of lid * lid 

let ghost loc_a = Loc.{ loc_a with loc_ghost = true } 
			  
let ppf = Format.err_formatter

let fold_map (|+>) map start l =
  List.fold_left
    (fun acc x -> acc |+> map x )
    start
    l
	    
type kind = List | Array | String | Bigarray
	    
module Cons = struct	    
    type t = { kind:kind; cons: string; nil: string}
    let default = "ll", { kind=List; cons="Cons"; nil="Nil" }
   		  
  end
let nil c = c.Cons.nil
let cons c = c.Cons.cons
		
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


module Array_indices = struct

    let map_2_2 ~lbl f g= function
      | [l1,e1;l2,e2] -> [lbl l1, f e1; lbl l2, g e2]
      | l -> l

    let map_2_3 ~lbl f g = function
      | [l1,e1;l2,e2;l3,e3] -> [lbl l1, f e1;lbl l2, g e2; lbl l3, f e3]
      | l -> l
	
let identify_lid lid =
  match lid with
  | Lident ".()" 
  | Ldot( Lident "Array", ("get"|"unsafe_get") )
    -> Some (Array, map_2_2)
  | Lident ".()<-"
  | Ldot( Lident "Array", ("set"|"unsafe_set") )
    -> Some (Array, map_2_3) 
  | Lident ".[]" 
  | Ldot( Lident "String", ("get"|"unsafe_get") ) ->
     Some (String, map_2_2)
  | Lident ".[]<-"
  | Ldot( Lident "String", ("set"|"unsafe_set") )
    -> Some (String, map_2_3) 
  | Lident ".{}" 
  | Ldot( Ldot ( Lident "Bigarray", "Array1" ) , ("get"|"unsafe_get") ) ->
     Some (Bigarray, map_2_2)
  | Lident ".{}<-"
  | Ldot( Ldot ( Lident "Bigarray", "Array1" ), ("set"|"unsafe_set") )
    -> Some (Bigarray, map_2_3)
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
  let open Cons in
  match lid.txt with
  | Lident "::" ->  { lid with txt = Lident cons.cons }
  | Lident "[]" -> { lid with txt = Lident cons.nil }
  | _ -> lid

module Interpreter = struct

type microtype = Kind of kind | Constructor of string
    
let var pat = match pat.ppat_desc with
  | Ppat_var {Loc.txt;loc} -> txt
  | _ -> assert false

let const_string e= match e.pexp_desc with
  | Pexp_constant ( Asttypes.Const_string(s, _ ) ) -> s
  | _ -> assert false

let constructor e = match e.pexp_desc with
  | Pexp_construct(llid,None) -> llid.Loc.txt
  | _ -> assert false

let kind = function
  | Lid.Lident x -> (
    match x with
    | "List"-> List
    | "Array" -> Array
    | "String" -> String
    | "Bigarray" -> Bigarray
    | _ -> assert false
  )
  | _ -> assert false
		
let field (llid,e) =
  let open Lid in
  match llid.Loc.txt with
  | Lident "kind" -> "kind" , Kind( kind @@ constructor e )
  | Lident ("cons" as s) | Lident ("nil" as s)  -> s, Constructor(const_string e)
  | _ -> assert false

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
  Cons.{ kind; cons; nil }
		
let record e = match e.pexp_desc with
  | Pexp_record (l, None ) ->
     let open Defs in
     let named = fold_map (|+>) field empty l in
     reconstruct named  
  | _ -> assert false
	   
    
let binding b =
    var b.pvb_pat,
    record b.pvb_expr
	   
end

module Expr_seq = struct
    
    let mk_nil cons nil_loc =
      let loc = ghost nil_loc in
      let lid =Loc.{txt = Lident (nil cons) ; loc } in
      H.Exp.construct ~loc lid None

    let mk_cons cons loc e1 e2 =
      let loc = ghost loc in
      let constr = Loc.{txt = Lident cons.Cons.cons; loc} in
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
  | Pexp_apply (f, args) ->
     let f = rm_env mapper.expr mapper env f in
     env,
     Array_indices.identify f
     >>=? (fun (kind,arg_map) ->Status.find_opt kind Env.(env.status)
     |>? ( fun cons ->
	 H.Exp.apply ~loc:expr.pexp_loc f @@
	   arg_map
	     ~lbl:(fun x -> x)
	     (rm_env mapper.expr mapper env)
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
