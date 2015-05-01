type 'a t = Cons of 'a * 'a t | Nil
let rec iter f = function
  | Cons(a,l) -> f a; iter f l
  | Nil -> ()
				  
let l = [1;2;3;4]
let {listlike| a; b ;c; d |listlike} =
  Cons(1,
       Cons(2,
	    Cons(3,
		 Cons(4, Nil)
		)
	   )
      ) 
				  
let l = {listlike| 1 ; 2; 3; 4 |listlike}
let () = Format.printf "@["; iter (Format.printf "%d@;") l ; Format.printf"@]\n"
