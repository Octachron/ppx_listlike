(*[%listlike register "n"  ~nil:"Nil" ~cons:"Cons"];;
 *)
type z  =Zero_type
type 'a succ = Succ_type
		 

module Nlist = struct
    
    type ('a,_) t =
      | Cons: 'a * ('a,'nat) t -> ('a,'nat succ) t
      | Nil : ('a, z ) t
		       
    let rec iter: type nat. ('a->unit) -> ('a, nat) t -> unit =
      fun f -> function
      | [%ll? a::l ] -> f a; iter f l
      | [%ll? [] ] -> ()

		    
    let rec fold: type nat. ('acc->'elt->'acc) -> 'acc ->  ('elt, nat ) t -> 'acc =
      fun (|+>) start l ->
      match l with
      | [%ll? a::l ] -> fold (|+>) (start |+> a) l 
      | [%ll? [] ] -> start
  end
       
module Std_array = Array
module String = struct
  type ('dim,'elt) t = (int,'dim) Nlist.t * 'elt array
  let make shape elt =
    let len = Nlist.fold ( * ) 1 shape in
    shape, Array.make len elt

  let rec flat_indice: type nat.
  int-> int -> (int,nat) Nlist.t -> (int,nat) Nlist.t -> int =
    fun m total word shape ->
    let open Nlist in
    match%ll word, shape with
    | k::w2, d::s2 -> flat_indice (m*d) (k*m + total) w2 s2    
    | [], [] -> total      
			
  let get (sh,array) indices =
    Std_array.get array @@ flat_indice 1 0 indices sh
					     
  end

module MdA=String 		  

let%ppx_listlike md = { kind = String_indices; cons = "Nlist.Cons"; nil = "Nlist.Nil" } 
and nl = {kind=List; cons="Nlist.Cons"; nil="Nlist.Nil" }
			
let a  = MdA.make [%nl[2;3;4]] 3

let n = [%md a.[1;2;3] ];;		    

		    
	    
open Nlist
let%ppx_listlike longname = { kind = List; cons = "Cons"; nil="Nil" } 
		    
		    
let l =[%longname[1;2;3;4]];;

let%ll l2 = [5;6;7;8];;  

let l3 = [10]  

let print_list l = 
  Format.printf "@[%a@]\n" (fun ppf -> iter @@ Format.fprintf ppf "%d@;") l

let () =
  let%ppx_listlike nl = { kind=List; cons="Cons"; nil="Nil" } in
  let%nl l = [-1;-2;-4] in
  print_list l

	     
let () =
  Format.printf "@[%a@]\n" (fun ppf -> List.iter @@ Format.fprintf ppf "%d@;") l3 ;
  print_list l2
