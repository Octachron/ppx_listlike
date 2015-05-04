[%listlike register  ~nil:"Nil" "n" ~cons:"Cons"];;

type z  =Zero_type
type 'a succ = Succ_type
		 
type ('a,_) t =
  | Cons: 'a * ('a,'base -> 'result ) t -> ('a,'base -> 'result succ) t
  | Nil : ('a, 'base -> 'base ) t
	    
let rec iter: type z r. ('a->unit) -> ('a,z->r) t -> unit = fun f -> function
  | {n| a; l.. |n} -> f a; iter f l
  | {n| |n} -> ()
			       
let l = [1;2;3;4]
				  
let {n| a; b.. |n} = {n| 5 ; (let x = 2 in x); 3; 4 |n}
let l = {n| 1; b.. |n} 
			 
let () = Format.printf "@["; iter (Format.printf "%d@;") l ; Format.printf"@]\n"

