# Ppx_listlike

## List literals for custom types
The main objective of this ppx extension for ocaml is to make possible the use of the list literal syntax for custom types.

##Basic uses
The simplest use of this syntax extension is to define a type `t` with two constructors `Cons` and `Nil`. For instance, we can define an alternating list
```Ocaml
type ('a,'b) t = Nil | Cons of 'a * ('b,'a) t
```

We can then define a new value of type t by combining an `ll` extension point with a standard list literal:
```Ocaml
let n =[%ll[ 1; "One one"; 11; "Two one"; 21; "One two one one" ]]
```

Inside the extension point `[%ll ..]`, all lists `[e1;e2;..]` are rewritten to the expression `Cons(e1, Cons(e2, ..., Nil)...)`. The type of the list-like literal thus depends of the type of the constructors `Cons` and `Nil` in scope.

If we want to have normal lists nested inside an `ll`-extension point, we need to open the standard list `stdl`-extension point:
```Ocaml
let nested_list = [%ll [1234; [%stdl[1;2;3;4]]; 2; [%stdl[2]] ] ]
```
It is also possible to use list-like syntax extension inside pattern with `[ll?..]`:
```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g = function
  | [%ll? a::q ] -> [%ll (f a)::(map g f q)]
  | [%ll? [] ] -> [%ll [] ]
```
Another solution for this function would be to open the extension point at the
`function` level

```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =[%ll function
  | a::q -> (f a)::(map g f q)
  | [] -> []
]
```
or alternatively
```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =function%ll
  | a::q -> (f a)::(map g f q)
  | [] -> []
```

## Advanced uses
Inside the compiler, list literals of the form `[a;b;c]` are rewritten to
` :: (a, :: ( b, :: ( c, [] ) ) ) `. Inside this expression, the constructor `::` and `[]` are special constructors. Moreover, the constructor `[]` cannot be redefined.

To circumvent this limitation, ppx_listlike adds a mechanism to define list-like constructor rewriter. New rewriters can be defined inside a module by
```Ocaml
let%ppx_listlike nl = { cons="Cons_nl"; nil="Nil_nl"; kind=List } 
```
The fields `cons` and `nil` define the name of the constructors that will replace the `::` and `[]`. The `kind` field is defined to `List` for list-like constructor rewriter. Once this `nl` rewriter defined, list literals inside a `[%nl ..]
extension point will be replaced the corresponding "Cons_nl .. Nil_nl" construction.

For instance, the `ll` and `stdl` extension point used earlier are predefined constructor rewriters corresponding to:
```Ocaml
let%ppx_listlike ll = { cons="Cons"; nil="Nil"; kind=List }
and stdl = { cons = "::"; nil="[]"; kind=List }
```

It is also possible to define local rewriters active only inside an expression with a `let ... in` binding.

##Extremely experimental features
This ppx extension contains also few very experimental features exploring an alternative syntax/semantic for multidimensionnal indices for array-like type (i.e. array, string and bigarray). These features can be activated by first defining an array indices rewriter
```Ocaml
let%ppx_listlike mi = { cons="Cons"; nil="Nil"; kind=String_indices } 
```
Then, inside an [%mi..] extension point, the corresponding access operator
`[%mi s.[a;b] ]` will be rewritten to ` s.[Cons(a,Cons(b,Nil))]`.
