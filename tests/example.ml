type ('a,'b) t = Nil | Cons of 'a * ('b,'a) t

let n =[%ll[ 1; "One one"; 11; "Two one"; 21; "One two one one" ]]
let nested_list = [%ll [1234; [%stdl[1;2;3;4]]; 2; [%stdl[2]] ]]

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g = function
  | [%ll? a::q ] -> Cons(f a, map g f q)
  | [%ll? [] ] -> Nil

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =[%ll function
  | a::q -> (f a)::(map g f q)
  | [] -> []
 ]
		   
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =function%ll
  | a::q -> (f a)::(map g f q)
  | [] -> []

let%ppx_listlike nl = { cons="Cons_nl"; nil="Nil_nl"; kind=List }
let%ppx_listlike mi = { cons="Cons"; nil="Nil"; kind=String_indices } 
			
