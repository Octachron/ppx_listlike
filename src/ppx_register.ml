(* forker from compiler libs *)
open Parsetree
open Ast_helper
open Location

type transformer= {
    implem: structure -> structure;
    iface: signature -> signature;
  }		      

type 'ast nature = {
    extract_context : 'ast ->  (Longident.t Asttypes.loc * Parsetree.expression) list * 'ast;
    transform: transformer -> 'ast -> 'ast ;
    add_attribute: attribute -> 'ast -> 'ast;
    mk_error: Location.error -> 'ast
  }
		     
		      
let implem = {
    extract_context =
      ( function
	| {pstr_desc = Pstr_attribute ({txt = "ocaml.ppx.context"}, x)} :: l ->
	   Ppx_context.get_fields x, l
	| ast -> [], ast
      );
    transform = (fun transformer ast -> transformer.implem ast );
    add_attribute = (fun attr ast ->  Str.attribute attr :: ast );
    mk_error=
      (fun error -> [{pstr_desc = Pstr_extension (Ast_mapper.extension_of_error error, []);
		      pstr_loc  = Location.none}]
      )
  }
		     
let interface = {
    extract_context =
      (function
	| {psig_desc = Psig_attribute ({txt = "ocaml.ppx.context"}, x)} :: l ->
           Ppx_context.get_fields x, l
        | ast -> [], ast
      );		  
    transform =  (fun transformer ast -> transformer.iface ast );
    add_attribute =(fun attr ast ->  Sig.attribute attr :: ast );
    mk_error = ( fun error ->
          [{psig_desc = Psig_extension (Ast_mapper.extension_of_error error, []);
            psig_loc  = Location.none}]
	       )
      
  }
	       

let rewriter nature transformer ast =
  let delayed () =
    let fields,ast = nature.extract_context ast in
    Ppx_context.restore fields;
    let ast = nature.transform (transformer ()) ast in
    let fields = Ppx_context.update_cookies fields in
    nature.add_attribute (Ppx_context.mk fields) ast in
  try delayed() with
    exn ->
    match error_of_exn exn with
    | Some error -> nature.mk_error error
    | None -> raise exn 
  
    
let apply_lazy ~source ~target transformer =
  let ic = open_in_bin source in
  let magic =
    really_input_string ic (String.length Config.ast_impl_magic_number)
  in

  let rewrite nature =
    let transform ast = rewriter nature transformer ast in
    Location.input_name := input_value ic;
    let ast = input_value ic in
    close_in ic;
    let ast = transform ast in
    let oc = open_out_bin target in
    output_string oc magic;
    output_value oc !Location.input_name;
    output_value oc ast;
    close_out oc
  and fail () =
    close_in ic;
    failwith "Ast_mapper: OCaml version mismatch or malformed input";
  in

  if magic = Config.ast_impl_magic_number then
    rewrite implem
  else if magic = Config.ast_intf_magic_number then
    rewrite interface
  else fail ()
    
let run_main transformer =
  try
    let a = Sys.argv in
    let n = Array.length a in
    if n > 2 then
      let transformer () =
	transformer (Array.to_list (Array.sub a 1 (n - 3)))
      in
      apply_lazy ~source:a.(n - 2) ~target:a.(n - 1) transformer
    else begin
      Printf.eprintf "Usage: %s [extra_args] <infile> <outfile>\n%!"
                     Sys.executable_name;
      exit 2
    end
  with exn ->
    prerr_endline (Printexc.to_string exn);
    exit 2

let register_function = ref (fun (_name:string) f -> run_main f)
let register name f = !register_function name f
