let a  = Array.make 10 3
let _ = a.(1;2;3);;		    

(*[%listlike register "n"  ~nil:"Nil" ~cons:"Cons"];;
 *)
type z  =Zero_type
type 'a succ = Succ_type
		 
type ('a,_) t =
  | Cons: 'a * ('a,'base -> 'result ) t -> ('a,'base -> 'result succ) t
  | Nil : ('a, 'base -> 'base ) t
	    
let rec iter: type z r. ('a->unit) -> ('a,z->r) t -> unit = fun f -> function
  | [%ll? a::l] -> f a; iter f l
  | [%ll?[]] -> ()
			       
let l =[%ll[1;2;3;4]];;

  
let () = Format.printf "@["; iter (Format.printf "%d@;") l ; Format.printf"@]\n"

