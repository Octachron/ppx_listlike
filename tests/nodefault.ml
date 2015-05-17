type ('a,'b) t = Nil | Cons of 'a * ('b,'a) t

let%ppx_listlike alt = { kind=List; cons="Cons"; nil="Nil" }

let n =[%alt 1; "One one"; 11; "Two one"; 21; "One two one one"]
let nested_list =
  let inner = [2;3] in 
  [%alt 1234; [1;2;3;4]; 2; [2]; 23; inner ]

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g = function
  | [%alt? a::q ] -> Cons(f a, map g f q)
  | [%alt? [] ] -> [%alt]

(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =[%with_alt function
  | a::q -> (f a)::(map g f q)
  | [] -> []
]		   
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =function%with_alt
  | a::q -> (f a)::(map g f q)
  | [] -> []

let%ppx_listlike nl = { alt with cons="Cons_nl"; nil="Nil_nl" }
and mi = { alt with kind=String_indices } 
			
