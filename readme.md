# Ppx_listlike

## List literals for custom types
The main objective of this ppx extension for ocaml is to make possible the use of the list literal syntax for custom types.

##List literals
The simplest use of this syntax extension is to define a type `t` with two constructors `Cons` and `Nil`. For instance, we can define an alternating list
```Ocaml
type ('a,'b) t = Nil | Cons of 'a * ('b,'a) t
```

We can then define a new value of type t by combining an `ll` extension point with a standard list literal:
```Ocaml
let n =[%ll 1; "One one"; 11; "Two one"; 21; "One two one one" ]
```

Inside the extension point `[%ll ..]`, the sequence of expression `e1;e2;..` is rewritten to the expression `Cons(e1, Cons(e2, ..., Nil)...)`. The type of the list-like literal thus depends of the type of the constructors `Cons` and `Nil` in scope.

##Pattern matching and [%with_ll ..] extension nodes

It is also possible to use list-like syntax extension inside pattern with `[with_ll?..]`:
```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g = function
  | [%with_ll? a::q ] -> Cons(f a, map g f q)]
  | [%with_ll? [] ] -> []
```
However, the behavior of the `[%with_ll? ..]` is slightly different from the behavior of `[%ll .. ]`. Inside the extension node `[%with_ll? ..]`, *all* list literals `[e1;e2;..]` are rewritten to `Cons(.., Nil)`. Similarly *all* expressions or patterns of the form `a::q` are transformed to `Cons(a,q)`.

The `[%with_ll ..]` extension node can be used outside of patterns by removing the trailing `?` which marks a pattern extension node. For instance, we could rewrite the previous `map` function as
```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let rec map f g =[%with_ll function
  | a::q -> (f a)::(map g f q)
  | [] -> []
]
```
Another solution for this function would be to open the extension point at the
`let` level using the shortcut syntax for extension node
```Ocaml
(* map : ('a,'b) t -> ('a->'c) -> ('b->'d) -> ('c,'d) t *)
let%with_ll rec map f g =function
  | a::q -> (f a)::(map g f q)
  | [] -> []
```

If we want to have normal lists nested inside an `[%with_ll .. ]` extension node, we need to use a standard list `[%stdl ..]`-extension node:
```Ocaml
let%with_ll nested_list = [1234; [%stdl 1;2;3;4 ]; 2; [%stdl 2] ]
```

##Pattern matching shortcut

For the sake of brevity, the `[%with_ll? ..]` extension node for pattern matching can be actually written `[%ll? .. ]`. However, in this case `[%ll?..]` is semantically only a shortcut for the [%with_ll?..] syntax.

## Advanced uses
Inside the compiler, list literals of the form `[a;b;c]` are rewritten to
` :: (a, :: ( b, :: ( c, [] ) ) ) `. Inside this expression, the constructor `::` and `[]` are special constructors. Moreover, the constructor `[]` cannot be redefined.

To circumvent this limitation, ppx_listlike adds a mechanism to define list-like constructor rewriter. New rewriters can be defined inside a module by
```Ocaml
let%ppx_listlike nl = { cons="Cons_nl"; nil="Nil_nl"; kind=List } 
```
The fields `cons` and `nil` define the name of the constructors that will replace the `::` and `[]`. The `kind` field is defined to `List` for list-like constructor rewriter. Once this `nl` rewriter defined, list literals inside a `[%with_nl ..]`
extension point will be replaced the corresponding "Cons_nl .. Nil_nl" construction.
The simplified `[%nl .. ]` extension node implements a limited version of this rewriting mechanism which transforms an expression sequence `e1;e2;..` to the corresponding list literal.

For instance, the `ll` and `stdl` extension point used earlier are predefined constructor rewriters corresponding to:
```Ocaml
let%ppx_listlike ll = { cons="Cons"; nil="Nil"; kind=List }
and stdl = { cons = "::"; nil="[]"; kind=List }
```
For obvious reasons, a valid rewriter name can not start with a "with_" prefix. It is also possible to define local rewriters active only inside an expression with a `let ... in` binding. Moreover, standard syntax for record can be used but the value of the fields needs to be constant literals. For instance 
```Ocaml
let%ppx_listlike ex = { ll with cons = "Snoc"; nil = "Lin" }
```
is fine but 
```Ocaml
let not_a_literal = "Cons"
let%ppx_listlike ex = { ll with cons = not_a_litteral }
```
is not.

##Avoiding ppx interferences
If the predefined  `[%ll]` and `[%stdl]` rewriter interfers with some other ppx extensions, the `-nostd` option can be used to start `ppx_listlike` with no predefined rewriters. For findlib based build systems, the easiest way to pass this option is to use the `ppx_listlike.notsd ` subpackage (i.e. ` -pkg ppx_listlike.nostd ` rather than 
`-pkg ppx_listlike`).

##Extremely experimental features
This ppx extension contains also few very experimental features exploring an alternative syntax/semantic for multidimensionnal indices for array-like type (i.e. array, string and bigarray). These features can be activated by first defining an array indices rewriter
```Ocaml
let%ppx_listlike mi = { cons="Cons"; nil="Nil"; kind=String_indices } 
```
Then, inside an [%with_mi..] extension point, the corresponding access operator
`[%with_mi s.[a;b] ]` will be rewritten to ` s.[Cons(a,Cons(b,Nil))]`. The same feature is available for `string`, `array` abd `bigarray` indices through
respectively the `String_indices`, `Array_indices` and `Bigarray_indices` constructors.
