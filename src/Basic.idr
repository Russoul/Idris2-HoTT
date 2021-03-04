module Basic

infixl 0 $

%inline public export
($) : (a -> b) -> a -> b
($) f x = f x

public export
the : (a : Type) -> (x : a) -> a
the _ x = x

public export
id : a -> a
id x = x

public export
const : a -> b -> a
const x _ = x

infixl 1 .
infixl 1 `compose`

||| In the stdlib it is the (.) operator.
public export
compose : (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

||| Instead of going via the stdlib route of naming conventions,
||| we choose the (.) operator to denote the dependent function
||| composition. Also note that the order of the operands is reversed.
public export
(.) : {p : a -> Type}
   -> (f : (x : a) -> p x)
   -> {q : {x : a} -> p x -> Type}
   -> (g : {x : a} -> (y : p x) -> q {x} y)
   -> ((x : a) -> q {x} (f x))
f . g = \x => g (f x)

public export
domain : {a : Type} -> (a -> b) -> Type
domain _ = a

public export
codomain : {b : Type} -> (a -> b) -> Type
codomain _ = b

public export
typeOf : {a : Type} -> a -> Type
typeOf _ = a
