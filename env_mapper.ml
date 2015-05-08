open Location
open Parsetree
open Ast_helper
open Asttypes

       
type 'env t = {
  attribute: 'env t -> 'env  -> attribute -> 'env * attribute option;
  attributes: 'env t -> 'env -> attribute list -> attribute list;
  case: 'env t -> 'env -> case -> 'env * case option;
  cases: 'env t -> 'env ->  case list -> case list;
  class_declaration: 'env t -> 'env -> class_declaration -> class_declaration;
  class_description: 'env t -> 'env -> class_description -> 'env * class_description;
  class_expr: 'env t -> 'env -> class_expr -> class_expr;
  class_field: 'env t -> 'env -> class_field -> 'env * class_field;
  class_signature: 'env t -> 'env -> class_signature -> class_signature;
  class_structure: 'env t -> 'env -> class_structure -> class_structure;
  class_type: 'env t -> 'env -> class_type -> class_type;
  class_type_declaration: 'env t -> 'env -> class_type_declaration
                          -> 'env * class_type_declaration;
  class_type_field: 'env t -> 'env -> class_type_field -> 'env * class_type_field;
  constructor_declaration: 'env t -> 'env -> constructor_declaration
                           -> 'env * constructor_declaration;
  expr: 'env t -> 'env -> expression -> 'env * expression;
  extension: 'env t -> 'env -> extension -> extension;
  extension_constructor: 'env t -> 'env -> extension_constructor
                         -> 'env * extension_constructor;
  include_declaration: 'env t -> 'env -> include_declaration -> include_declaration;
  include_description: 'env t -> 'env -> include_description -> include_description;
  label_declaration: 'env t -> 'env -> label_declaration -> 'env * label_declaration;
  location: 'env t -> 'env -> Location.t -> Location.t;
  module_binding: 'env t -> 'env -> module_binding -> 'env * module_binding option;
  module_declaration: 'env t -> 'env -> module_declaration -> 'env * module_declaration;
  module_expr: 'env t -> 'env -> module_expr -> module_expr;
  module_type: 'env t -> 'env -> module_type -> module_type;
  module_type_declaration: 'env t -> 'env -> module_type_declaration
                           -> module_type_declaration;
  open_description: 'env t -> 'env -> open_description -> open_description;
  pat: 'env t -> 'env -> pattern -> 'env * pattern;
  payload: 'env t -> 'env -> payload -> payload;
  signature: 'env t -> 'env -> signature -> signature;
  signature_item: 'env t -> 'env -> signature_item -> 'env * signature_item option;
  structure: 'env t -> 'env -> structure -> structure;
  structure_item: 'env t -> 'env -> structure_item -> 'env * structure_item option;
  typ: 'env t -> 'env -> core_type -> 'env * core_type;
  type_declaration: 'env t -> 'env -> type_declaration -> 'env * type_declaration;
  type_extension: 'env t -> 'env -> type_extension -> type_extension;
  type_kind: 'env t -> 'env -> type_kind -> type_kind;
  value_binding: 'env t -> 'env -> value_binding -> 'env * value_binding option;
  value_description: 'env t -> 'env -> value_description -> value_description;
  with_constraint: 'env t -> 'env -> with_constraint -> 'env * with_constraint;
}


let rm_env sel_mapper mapper env obj =
  sel_mapper mapper env obj |> snd   
		
let map_fst f env (x, y) = let env, x' = f env x in env,(x', y)
let map_snd f env (x, y) = let env,y = f env y in env, (x, y)
let map_tuple f1 f2 (x, y) = (f1 x, f2 y)
let map_tuple__2 f1 f2 env (x, y) =
  let x = f1 env x in
  let env, y = f2 env y in
  env, ( x, y)

let map_tuple2_1 f1 f2 f3 (env1,env2,env3) (x, y, z) =
  let env1, x = f1 env1 x
  and env2, y = f2 env2 y
  and z = f3 env3 z in	  
  (env1,env2,env3),(x,y,z)

				      
module Opt =
  struct
    let (|>? ) x f = match x with
      | None -> None
      | Some x -> Some ( f x )
    let (><?) x default =
      match x with
      | None -> default
      | Some x -> x
  end
open Opt
let ( <=<  )  (env',x)  (env,acc) = (env',x::acc)     

let try_ x f = match snd @@ f x with
  | None -> x
  | Some x -> x
				      
let map_opt f = function None -> None | Some x -> Some (f x)

						       
let map_loc sub env {loc; txt} = {loc = sub.location sub env loc; txt}


let thread_env f env l =
  let env,l = List.fold_left (fun acc x -> f (fst acc) x <=< acc ) (env,[]) l in
  env, List.rev l
					
let thread f env l =
  let env, l = List.fold_left (fun acc x -> f (fst acc) x <=< acc ) (env,[]) l in
  List.rev l

let cons_opt x l = 
    match x with
    | None ->  l
    | Some x -> x::l
		  	  
let thread_opt f env l =
  let folder (env,l) x =
    let env, opt_x = f env x in
    env, cons_opt opt_x l
  in
  let env,l = List.fold_left folder (env,[]) l in
  List.rev l 
					
module T = struct
  (* Type expressions for the core language *)

  let row_field sub env = function
    | Rtag (l, attrs, b, tl) ->
       let env, tl = thread_env (sub.typ sub) env  tl in 
       env, Rtag (l, sub.attributes sub env attrs, b, tl )
    | Rinherit t -> let env, t = sub.typ sub env t in
		    env , Rinherit t

  let map sub env {ptyp_desc = desc; ptyp_loc = loc; ptyp_attributes = attrs} =
    let open Typ in
    let loc = sub.location sub env loc in
    let attrs = sub.attributes sub env attrs in
    let t = match desc with
      | Ptyp_any -> any ~loc ~attrs ()
      | Ptyp_var s -> var ~loc ~attrs s
      | Ptyp_arrow (lab, t1, t2) ->
         arrow ~loc ~attrs lab (rm_env sub.typ sub env t1) (rm_env sub.typ sub env t2)
      | Ptyp_tuple tyl -> tuple ~loc ~attrs (thread (sub.typ sub) env tyl)
      | Ptyp_constr (lid, tl) ->
         constr ~loc ~attrs (map_loc sub env lid) (thread (sub.typ sub) env tl)
      | Ptyp_object (l, o) ->
	 let f env (s, a, t) =
	   let env', t = sub.typ sub env t in
	   env', (s, sub.attributes sub env a, t) in
	 object_ ~loc ~attrs (thread f env l) o
      | Ptyp_class (lid, tl) ->
         class_ ~loc ~attrs (map_loc sub env lid) (thread (sub.typ sub) env tl)
      | Ptyp_alias (t, s) -> alias ~loc ~attrs (rm_env sub.typ sub env t) s
      | Ptyp_variant (rl, b, ll) ->
         variant ~loc ~attrs (thread (row_field sub) env rl) b ll
      | Ptyp_poly (sl, t) -> poly ~loc ~attrs sl (rm_env sub.typ sub env t)
      | Ptyp_package (lid, l) ->
         package ~loc ~attrs (map_loc sub env lid)
		 (thread (map_tuple__2 (map_loc sub) (sub.typ sub) )  env l )
      | Ptyp_extension x -> extension ~loc ~attrs (sub.extension sub env x)
    in env, t
		 
  let map_type_declaration sub env
      {ptype_name; ptype_params; ptype_cstrs;
       ptype_kind;
       ptype_private;
       ptype_manifest;
       ptype_attributes;
       ptype_loc} =
    env,
    Type.mk (map_loc sub env ptype_name)
      ~params:(thread (map_fst @@ sub.typ sub ) env ptype_params)
      ~priv:ptype_private
      ~cstrs:(thread
                (map_tuple2_1 (sub.typ sub) (sub.typ sub) (sub.location sub))
		(env,env,env)
                ptype_cstrs)
      ~kind:(sub.type_kind sub env ptype_kind)
      ?manifest:(ptype_manifest |>? rm_env sub.typ sub env)
      ~loc:(sub.location sub env ptype_loc)
      ~attrs:(sub.attributes sub env ptype_attributes)

  let map_type_kind sub env = function
    | Ptype_abstract -> Ptype_abstract
    | Ptype_variant l ->
        Ptype_variant (thread (sub.constructor_declaration sub) env l)
    | Ptype_record l -> Ptype_record (thread (sub.label_declaration sub) env l)
    | Ptype_open -> Ptype_open

  let map_constructor_arguments sub env l =
    thread (sub.typ sub) env l
 
  let map_type_extension sub env
      {ptyext_path; ptyext_params;
       ptyext_constructors;
       ptyext_private;
       ptyext_attributes} =
    Te.mk
      (map_loc sub env ptyext_path)
      (thread (sub.extension_constructor sub) env ptyext_constructors)
      ~params:(thread (map_fst @@ sub.typ sub) env ptyext_params)
      ~priv:ptyext_private
      ~attrs:(sub.attributes sub env ptyext_attributes)

  let map_extension_constructor_kind sub env = function
      Pext_decl(ctl, cto) ->
        Pext_decl(map_constructor_arguments sub env ctl, cto |>? rm_env sub.typ sub env)
    | Pext_rebind li ->
        Pext_rebind (map_loc sub env li)

  let map_extension_constructor sub env
      {pext_name;
       pext_kind;
       pext_loc;
       pext_attributes} =
    env, 
    Te.constructor
      (map_loc sub env pext_name)
      (map_extension_constructor_kind sub env pext_kind)
      ~loc:(sub.location sub env pext_loc)
      ~attrs:(sub.attributes sub env pext_attributes)

end

module CT = struct
  (* Type expressions for the class language *)

  let map sub env {pcty_loc = loc; pcty_desc = desc; pcty_attributes = attrs} =
    let open Cty in
    let loc = sub.location sub env loc in
    match desc with
    | Pcty_constr (lid, tys) ->
        constr ~loc ~attrs (map_loc sub env lid) (thread (sub.typ sub) env tys)
    | Pcty_signature x -> signature ~loc ~attrs (sub.class_signature sub env x)
    | Pcty_arrow (lab, t, ct) ->
        arrow ~loc ~attrs lab (rm_env sub.typ sub env t) (sub.class_type sub env ct)
    | Pcty_extension x -> extension ~loc ~attrs (sub.extension sub env x)

  let map_field sub env {pctf_desc = desc; pctf_loc = loc; pctf_attributes = attrs}
    =
    let open Ctf in
    let loc = sub.location sub env loc in
    env,
    match desc with
    | Pctf_inherit ct -> inherit_ ~loc ~attrs (sub.class_type sub env ct)
    | Pctf_val (s, m, v, t) -> val_ ~loc ~attrs s m v (rm_env sub.typ sub env t)
    | Pctf_method (s, p, v, t) -> method_ ~loc ~attrs s p v (rm_env sub.typ sub env t)
    | Pctf_constraint (t1, t2) ->
        constraint_ ~loc ~attrs (rm_env sub.typ sub env t1) (rm_env sub.typ sub env t2)
    | Pctf_attribute x -> attribute ~loc ( try_ x @@ sub.attribute sub env )
    | Pctf_extension x -> extension ~loc ~attrs (sub.extension sub env x)

  let map_signature sub env {pcsig_self; pcsig_fields} =
    Csig.mk
      (rm_env sub.typ sub env pcsig_self)
      (thread (sub.class_type_field sub) env pcsig_fields)
end

module MT = struct
  (* Type expressions for the module language *)

  let map sub env {pmty_desc = desc; pmty_loc = loc; pmty_attributes = attrs} =
    let open Mty in
    let loc = sub.location sub env loc in
    let attrs = sub.attributes sub env attrs in
    let mt = match desc with
      | Pmty_ident s -> ident ~loc ~attrs (map_loc sub env s)
      | Pmty_alias s -> alias ~loc ~attrs (map_loc sub env s)
      | Pmty_signature sg -> signature ~loc ~attrs (sub.signature sub env sg)
      | Pmty_functor (s, mt1, mt2) ->
         functor_ ~loc ~attrs (map_loc sub env s)
		  ( mt1 |>? (sub.module_type sub env) )
		  (sub.module_type sub env mt2)
      | Pmty_with (mt, l) ->
	 with_ ~loc ~attrs (sub.module_type sub env mt)
	       (thread (sub.with_constraint sub) env l)
      | Pmty_typeof me -> typeof_ ~loc ~attrs (sub.module_expr sub env me)
      | Pmty_extension x -> extension ~loc ~attrs (sub.extension sub env x)
    in
    mt
				    
  let map_with_constraint sub env mt = env, match mt with
    | Pwith_type (lid, d) ->
        Pwith_type (map_loc sub env lid, rm_env sub.type_declaration sub env d)
    | Pwith_module (lid, lid2) ->
        Pwith_module (map_loc sub env lid, map_loc sub env lid2)
    | Pwith_typesubst d -> Pwith_typesubst (rm_env sub.type_declaration sub env d)
    | Pwith_modsubst (s, lid) ->
        Pwith_modsubst (map_loc sub env s, map_loc sub env lid)

  let map_signature_item sub env {psig_desc = desc; psig_loc = loc} =
    let open Sig in
    let loc = sub.location sub env loc in
    let msi =  match desc with
      | Psig_value vd -> value ~loc (sub.value_description sub env vd)
      | Psig_type ((*rf,*) l) -> type_ ~loc (*rf*) (thread (sub.type_declaration sub) env l)
      | Psig_typext te -> type_extension ~loc (sub.type_extension sub env te)
      | Psig_exception ed -> exception_ ~loc (rm_env sub.extension_constructor sub env ed)
      | Psig_module x -> module_ ~loc (rm_env sub.module_declaration sub env x)
      | Psig_recmodule l ->
         rec_module ~loc (thread (sub.module_declaration sub) env l)
      | Psig_modtype x -> modtype ~loc (sub.module_type_declaration sub env x)
      | Psig_open x -> open_ ~loc (sub.open_description sub env x)
      | Psig_include x -> include_ ~loc (sub.include_description sub env x)
      | Psig_class l -> class_ ~loc (thread (sub.class_description sub) env l)
      | Psig_class_type l ->
        class_type ~loc (thread (sub.class_type_declaration sub) env l)
      | Psig_extension (x, attrs) ->
         extension ~loc (sub.extension sub env x) ~attrs:(sub.attributes sub env attrs)
      | Psig_attribute x -> attribute ~loc ( try_ x @@ sub.attribute sub env )
    in env, Some msi
  end


module M = struct
  (* Value expressions for the module language *)

  let map sub env {pmod_loc = loc; pmod_desc = desc; pmod_attributes = attrs} =
    let open Mod in
    let loc = sub.location sub env loc in
    let attrs = sub.attributes sub env attrs in
    match desc with
    | Pmod_ident x -> ident ~loc ~attrs (map_loc sub env x)
    | Pmod_structure str -> structure ~loc ~attrs (sub.structure sub env str)
    | Pmod_functor (arg, arg_ty, body) ->
        functor_ ~loc ~attrs (map_loc sub env arg)
          ( arg_ty |>? sub.module_type sub env )
          (sub.module_expr sub env body)
    | Pmod_apply (m1, m2) ->
        apply ~loc ~attrs (sub.module_expr sub env m1) (sub.module_expr sub env m2)
    | Pmod_constraint (m, mty) ->
        constraint_ ~loc ~attrs (sub.module_expr sub env m)
                    (sub.module_type sub env mty)
    | Pmod_unpack e -> unpack ~loc ~attrs (rm_env sub.expr sub env e)
    | Pmod_extension x -> extension ~loc ~attrs (sub.extension sub env x)

  let map_structure_item sub env {pstr_loc = loc; pstr_desc = desc} =
    let open Str in
    let loc = sub.location sub env loc in
    let si = match desc with
      | Pstr_eval (x, attrs) ->
	 eval ~loc ~attrs:(sub.attributes sub env attrs) (rm_env sub.expr sub env x)
      | Pstr_value (r, vbs) -> value ~loc r (thread_opt (sub.value_binding sub) env vbs)
      | Pstr_primitive vd -> primitive ~loc (sub.value_description sub env vd)
      | Pstr_type l -> type_ ~loc (thread (sub.type_declaration sub) env l)
      | Pstr_typext te -> type_extension ~loc (sub.type_extension sub env  te)
      | Pstr_exception ed -> exception_ ~loc (rm_env sub.extension_constructor sub env ed)
      | Pstr_module x -> module_ ~loc ( try_ x @@ sub.module_binding sub env )
      | Pstr_recmodule l -> rec_module ~loc (thread_opt (sub.module_binding sub) env l)
      | Pstr_modtype x -> modtype ~loc (sub.module_type_declaration sub env x)
      | Pstr_open x -> open_ ~loc (sub.open_description sub env x)
      | Pstr_class l -> class_ ~loc (List.map (sub.class_declaration sub env) l)
      | Pstr_class_type l ->
         class_type ~loc (thread (sub.class_type_declaration sub) env l)
      | Pstr_include x -> include_ ~loc (sub.include_declaration sub env x)
      | Pstr_extension (x, attrs) ->
         extension ~loc (sub.extension sub env x) ~attrs:(sub.attributes sub env attrs)
      | Pstr_attribute x -> attribute ~loc ( try_ x @@ sub.attribute sub env ) in
    env, Some si
end

module E = struct
  (* Value expressions for the core language *)

  let map sub env {pexp_loc = loc; pexp_desc = desc; pexp_attributes = attrs} =
    let open Exp in
    let loc = sub.location sub env loc in
    let attrs = sub.attributes sub env attrs in
    env,
    match desc with
    | Pexp_ident x -> ident ~loc ~attrs (map_loc sub env x)
    | Pexp_constant x -> constant ~loc ~attrs x
    | Pexp_let (r, vbs, e) ->
        let_ ~loc ~attrs r (thread_opt (sub.value_binding sub) env vbs)
          ( rm_env sub.expr sub env e)
    | Pexp_fun (lab, def, p, e) ->
        fun_ ~loc ~attrs lab ( def |>? rm_env sub.expr sub env) (rm_env sub.pat sub env p)
          (rm_env sub.expr sub env e)
    | Pexp_function pel -> function_ ~loc ~attrs (sub.cases sub env pel)
    | Pexp_apply (e, l) ->
        apply ~loc ~attrs ( rm_env sub.expr sub env e) ( thread (map_snd @@ sub.expr sub) env l)
    | Pexp_match (e, pel) ->
        match_ ~loc ~attrs ( rm_env sub.expr sub env e) (sub.cases sub env pel)
    | Pexp_try (e, pel) -> try_ ~loc ~attrs ( rm_env sub.expr sub env e) (sub.cases sub env pel)
    | Pexp_tuple el -> tuple ~loc ~attrs (thread (sub.expr sub) env el)
    | Pexp_construct (lid, arg) ->
       construct ~loc ~attrs (map_loc sub env lid)
		 ( arg |>? rm_env sub.expr sub env)
    | Pexp_variant (lab, eo) ->
        variant ~loc ~attrs lab ( eo |>? rm_env sub.expr sub env )
    | Pexp_record (l, eo) ->
        record ~loc ~attrs (thread (map_tuple__2 (map_loc sub) (sub.expr sub)) env l)
          (eo |>? rm_env sub.expr sub env)
    | Pexp_field (e, lid) ->
        field ~loc ~attrs (rm_env sub.expr sub env e) (map_loc sub env lid)
    | Pexp_setfield (e1, lid, e2) ->
        setfield ~loc ~attrs (rm_env sub.expr sub env e1) (map_loc sub env lid)
          (rm_env sub.expr sub env e2)
    | Pexp_array el -> array ~loc ~attrs (thread (sub.expr sub) env el)
    | Pexp_ifthenelse (e1, e2, e3) ->
        ifthenelse ~loc ~attrs ( rm_env sub.expr sub env e1) ( rm_env sub.expr sub env e2)
          ( e3 |>? rm_env sub.expr sub env )
    | Pexp_sequence (e1, e2) ->
       let env, e1 = sub.expr sub env e1 in
        sequence ~loc ~attrs e1 (rm_env sub.expr sub env e2)
    | Pexp_while (e1, e2) ->
        while_ ~loc ~attrs ( rm_env sub.expr sub env e1) ( rm_env sub.expr sub env e2)
    | Pexp_for (p, e1, e2, d, e3) ->
        for_ ~loc ~attrs (rm_env sub.pat sub env p) (rm_env sub.expr sub env e1) ( rm_env sub.expr sub env e2) d
          (rm_env sub.expr sub env e3)
    | Pexp_coerce (e, t1, t2) ->
       coerce ~loc ~attrs (rm_env sub.expr sub env e)
	      ( t1 |>? rm_env sub.typ sub env)
          ( rm_env sub.typ sub env t2)
    | Pexp_constraint (e, t) ->
       constraint_ ~loc ~attrs (rm_env sub.expr sub env e)
		   (rm_env sub.typ sub env t)
    | Pexp_send (e, s) -> send ~loc ~attrs (rm_env sub.expr sub env e) s
    | Pexp_new lid -> new_ ~loc ~attrs (map_loc sub env lid)
    | Pexp_setinstvar (s, e) ->
        setinstvar ~loc ~attrs (map_loc sub env s) (rm_env sub.expr sub env e)
    | Pexp_override sel ->
        override ~loc ~attrs
          (thread (map_tuple__2 (map_loc sub) (sub.expr sub)) env sel)
    | Pexp_letmodule (s, me, e) ->
        letmodule ~loc ~attrs (map_loc sub env s) (sub.module_expr sub env me)
          (rm_env sub.expr sub env e)
    | Pexp_assert e -> assert_ ~loc ~attrs (rm_env sub.expr sub env e)
    | Pexp_lazy e -> lazy_ ~loc ~attrs (rm_env sub.expr sub env e)
    | Pexp_poly (e, t) ->
        poly ~loc ~attrs (rm_env sub.expr sub env e) (t |>? rm_env sub.typ sub env )
    | Pexp_object cls -> object_ ~loc ~attrs (sub.class_structure sub env cls)
    | Pexp_newtype (s, e) -> newtype ~loc ~attrs s (rm_env sub.expr sub env e)
    | Pexp_pack me -> pack ~loc ~attrs (sub.module_expr sub env me)
    | Pexp_open (ovf, lid, e) ->
        open_ ~loc ~attrs ovf (map_loc sub env lid) (rm_env sub.expr sub env e)
    | Pexp_extension x -> extension ~loc ~attrs (sub.extension sub env x)
end

module P = struct
  (* Patterns *)

  let map sub env {ppat_desc = desc; ppat_loc = loc; ppat_attributes = attrs} =
    let open Pat in
    let loc = sub.location sub env loc in
    let attrs = sub.attributes sub env attrs in
    env,
    match desc with
    | Ppat_any -> any ~loc ~attrs ()
    | Ppat_var s -> var ~loc ~attrs (map_loc sub env s)
    | Ppat_alias (p, s) -> alias ~loc ~attrs (rm_env sub.pat sub env p) (map_loc sub env s)
    | Ppat_constant c -> constant ~loc ~attrs c
    | Ppat_interval (c1, c2) -> interval ~loc ~attrs c1 c2
    | Ppat_tuple pl -> tuple ~loc ~attrs (thread (sub.pat sub) env pl)
    | Ppat_construct (l, p) ->
        construct ~loc ~attrs (map_loc sub env l) ( p |>? rm_env sub.pat sub env )
    | Ppat_variant (l, p) -> variant ~loc ~attrs l ( p|>? rm_env sub.pat sub env )
    | Ppat_record (lpl, cf) ->
        record ~loc ~attrs
               (thread (map_tuple__2 (map_loc sub) (sub.pat sub)) env lpl) cf
    | Ppat_array pl -> array ~loc ~attrs (thread (sub.pat sub) env pl)
    | Ppat_or (p1, p2) ->
       let env,p1 = sub.pat sub env p1 in
       or_ ~loc ~attrs p1 (rm_env sub.pat sub env p2)
    | Ppat_constraint (p, t) ->
        constraint_ ~loc ~attrs ( rm_env sub.pat sub env p) ( rm_env sub.typ sub env t)
    | Ppat_type s -> type_ ~loc ~attrs (map_loc sub env s)
    | Ppat_lazy p -> lazy_ ~loc ~attrs (rm_env sub.pat sub env p)
    | Ppat_unpack s -> unpack ~loc ~attrs (map_loc sub env s)
    | Ppat_exception p -> exception_ ~loc ~attrs ( rm_env sub.pat sub env p)
    | Ppat_extension x -> extension ~loc ~attrs (sub.extension sub env x)
end

module CE = struct
  (* Value expressions for the class language *)

  let map sub env {pcl_loc = loc; pcl_desc = desc; pcl_attributes = attrs} =
    let open Cl in
    let loc = sub.location sub env loc in
    match desc with
    | Pcl_constr (lid, tys) ->
        constr ~loc ~attrs (map_loc sub env lid) (thread (sub.typ sub) env tys)
    | Pcl_structure s ->
        structure ~loc ~attrs (sub.class_structure sub env s)
    | Pcl_fun (lab, e, p, ce) ->
        fun_ ~loc ~attrs lab
          ( e |>? rm_env sub.expr sub env)
          (rm_env sub.pat sub env p)
          (sub.class_expr sub env ce)
    | Pcl_apply (ce, l) ->
        apply ~loc ~attrs (sub.class_expr sub env ce)
          (thread (map_snd (sub.expr sub)) env l)
    | Pcl_let (r, vbs, ce) ->
        let_ ~loc ~attrs r (thread_opt (sub.value_binding sub) env vbs)
          (sub.class_expr sub env ce)
    | Pcl_constraint (ce, ct) ->
        constraint_ ~loc ~attrs (sub.class_expr sub env ce) (sub.class_type sub env ct)
    | Pcl_extension x -> extension ~loc ~attrs (sub.extension sub env x)

  let map_kind sub env = function
    | Cfk_concrete (o, e) -> Cfk_concrete (o, rm_env sub.expr sub env e)
    | Cfk_virtual t -> Cfk_virtual ( rm_env sub.typ sub env t)

  let map_field sub env {pcf_desc = desc; pcf_loc = loc; pcf_attributes = attrs} =
    let open Cf in
    let loc = sub.location sub env loc in
    ( env, 
      match desc with
      | Pcf_inherit (o, ce, s) -> inherit_ ~loc ~attrs o (sub.class_expr sub env ce) s
      | Pcf_val (s, m, k) -> val_ ~loc ~attrs (map_loc sub env s) m (map_kind sub env k)
      | Pcf_method (s, p, k) ->
         method_ ~loc ~attrs (map_loc sub env s) p (map_kind sub env k)
      | Pcf_constraint (t1, t2) ->
         constraint_ ~loc ~attrs (rm_env sub.typ sub env t1) (rm_env sub.typ sub env t2)
      | Pcf_initializer e -> initializer_ ~loc ~attrs (rm_env sub.expr sub env e)
      | Pcf_attribute x -> attribute ~loc (try_ x @@ sub.attribute sub env)
      | Pcf_extension x -> extension ~loc ~attrs (sub.extension sub env x)
    )
      
  let map_structure sub env {pcstr_self; pcstr_fields} =
    {
      pcstr_self = rm_env sub.pat sub env pcstr_self;
      pcstr_fields = thread (sub.class_field sub) env pcstr_fields;
    }

  let class_infos sub env f {pci_virt; pci_params = pl; pci_name; pci_expr;
                             pci_loc; pci_attributes} =
    env,
    Ci.mk
     ~virt:pci_virt
     ~params:(thread (map_fst (sub.typ sub)) env pl)
      (map_loc sub env pci_name)
      (f env pci_expr)
      ~loc:(sub.location sub env pci_loc)
      ~attrs:(sub.attributes sub env pci_attributes)
end

(* Now, a generic AST mapper, to be extended to cover all kinds and
   cases of the OCaml grammar.  The default behavior of the mapper is
   the identity. *)


let value_description
      this env
      {pval_name; pval_type; pval_prim; pval_loc; pval_attributes} =
        Val.mk
          (map_loc this env pval_name)
          (rm_env this.typ this env pval_type)
          ~attrs:(this.attributes this env pval_attributes)
          ~loc:(this.location this env pval_loc)
          ~prim:pval_prim

let module_declaration
  this env {pmd_name; pmd_type; pmd_attributes; pmd_loc} =
       env,
         Md.mk
           (map_loc this env pmd_name)
           (this.module_type this env pmd_type)
           ~attrs:(this.attributes this env pmd_attributes)
           ~loc:(this.location this env pmd_loc)

let module_type_declaration
      this env {pmtd_name; pmtd_type; pmtd_attributes; pmtd_loc} =
  Mtd.mk
    (map_loc this env pmtd_name)
    ?typ:(map_opt (this.module_type this env) pmtd_type)
    ~attrs:(this.attributes this env pmtd_attributes)
    ~loc:(this.location this env pmtd_loc)
    
	  
	      
let identity =
  {
    structure = (fun this env l -> thread_opt (this.structure_item this) env l);
    structure_item = M.map_structure_item;
    module_expr = M.map;
    signature = (fun this env l -> thread_opt (this.signature_item this) env l);
    signature_item = MT.map_signature_item;
    module_type = MT.map;
    with_constraint = MT.map_with_constraint;
    class_declaration =
      (fun this env ci -> snd @@ CE.class_infos this env (this.class_expr this) ci );
    class_expr = CE.map;
    class_field = CE.map_field;
    class_structure = CE.map_structure;
    class_type = CT.map;
    class_type_field = CT.map_field;
    class_signature = CT.map_signature;
    class_type_declaration =
      (fun this env-> CE.class_infos this env (this.class_type this));
    class_description =
      (fun this env-> CE.class_infos this env (this.class_type this));
    type_declaration = T.map_type_declaration;
    type_kind = T.map_type_kind;
    typ = T.map;
    type_extension = T.map_type_extension;
    extension_constructor = T.map_extension_constructor;
    value_description;

    pat = P.map;
    expr = E.map;

    module_declaration;
    module_type_declaration;

    module_binding =
      (fun this env {pmb_name; pmb_expr; pmb_attributes; pmb_loc} ->
       env,
       Some(
           Mb.mk (map_loc this env pmb_name) (this.module_expr this env pmb_expr)
		 ~attrs:(this.attributes this env pmb_attributes)
		 ~loc:(this.location this env pmb_loc)
	 )
      );


    open_description =
      (fun this env {popen_lid; popen_override; popen_attributes; popen_loc} ->
         Opn.mk (map_loc this env popen_lid)
           ~override:popen_override
           ~loc:(this.location this env popen_loc)
           ~attrs:(this.attributes this env popen_attributes)
      );


    include_description =
      (fun this env {pincl_mod; pincl_attributes; pincl_loc} ->
         Incl.mk (this.module_type this env pincl_mod)
           ~loc:(this.location this env pincl_loc)
           ~attrs:(this.attributes this env pincl_attributes)
      );

    include_declaration =
      (fun this env {pincl_mod; pincl_attributes; pincl_loc} ->
         Incl.mk (this.module_expr this env pincl_mod)
           ~loc:(this.location this env pincl_loc)
           ~attrs:(this.attributes this env pincl_attributes)
      );


    value_binding =
      (fun this env {pvb_pat; pvb_expr; pvb_attributes; pvb_loc} ->
       env,
       Some (
           Vb.mk
             ( rm_env this.pat this env pvb_pat)
             ( rm_env this.expr this env pvb_expr)
             ~loc:(this.location this env pvb_loc)
             ~attrs:(this.attributes this env pvb_attributes)
	 )
	      );


    constructor_declaration =
      (fun this env {pcd_name; pcd_args; pcd_res; pcd_loc; pcd_attributes} ->
       env, 
        Type.constructor
          (map_loc this env pcd_name)
          ~args:(T.map_constructor_arguments this env pcd_args)
          ?res:(pcd_res |>? rm_env this.typ this env )
          ~loc:(this.location this env pcd_loc)
          ~attrs:(this.attributes this env pcd_attributes)
      );

    label_declaration =
      (fun this env {pld_name; pld_type; pld_loc; pld_mutable; pld_attributes} ->
       env,
         Type.field
           (map_loc this env pld_name)
           (rm_env this.typ this env pld_type)
           ~mut:pld_mutable
           ~loc:(this.location this env pld_loc)
           ~attrs:(this.attributes this env pld_attributes)
      );

    cases = (fun this env l -> thread_opt (this.case this) env l);
    case =
      (fun this env {pc_lhs; pc_guard; pc_rhs} ->
       env,
       Some
         {
           pc_lhs = rm_env this.pat this env pc_lhs;
           pc_guard = pc_guard |>? rm_env this.expr this env;
           pc_rhs = rm_env this.expr this env pc_rhs;
         }
      );



    location = (fun this env l -> l);

    extension = (fun this env (s, e) -> (map_loc this env s, this.payload this env e));
    attribute = (fun this env (s, e) -> env, Some (map_loc this env s, this.payload this env e));
    attributes = (fun this env l -> thread_opt (this.attribute this) env l);
    payload =
      (fun this env-> function
         | PStr x -> PStr (this.structure this env x)
         | PTyp x -> PTyp ( rm_env this.typ this env x)
         | PPat (x, g) -> PPat ( rm_env this.pat this env  x, g |>? rm_env this.expr this env)
      );
  }

let to_transform env env_mapper =
  Ppx_register.{
      implem = (fun structure -> env_mapper.structure env_mapper env structure);
      iface = (fun signature -> env_mapper.signature env_mapper env signature);
  }
    
