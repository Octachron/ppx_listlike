type ('a,'b) t = Nil | Cons of 'a * ('b,'a) t

let n =[%ll 1; "One one"; 11; "Two one"; 21; "One two one one"]
let nested_list =
  let inner = [2;3] in 
  [%ll 1234; [1;2;3;4]; 2; [2]; 23; inner ]

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g = function
  | [%ll? a::q ] -> Cons(f a, map g f q)
  | [%ll? [] ] -> [%ll]

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
(*let rec map f g =[%ll function
  | a::q -> (f a)::(map g f q)
  | [] -> []
]		   
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =function
  | a::q -> (f a)::(map g f q)
  | [] -> []
*)
let%ppx_listlike nl = { cons="Cons_nl"; nil="Nil_nl"; kind=List }
and mi = { cons="Cons"; nil="Nil"; kind=String_indices } 
			
