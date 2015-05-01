type 'a t = Cons of 'a * 'a t | Nil
let rec iter f = function
  | Cons(a,l) -> f a; iter f l
  | Nil -> ()
				  
let l = [1;2;3;4]
let l2 =
  Cons(1,
       Cons(2,
	    Cons(3,
		 Cons(4, Nil)
		)
	   )
      ) 
				  
let l = {listlike| {listlike_| 1; 2|listlike_} ; {listlike_|3; 4|listlike_} |listlike}
let () = Format.printf "@["; iter (Format.printf "%s@;") l ; Format.printf"@]\n"
