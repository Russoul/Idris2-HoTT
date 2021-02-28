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

public export
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

public export
domain : {a : Type} -> (a -> b) -> Type
domain _ = a

public export
codomain : {b : Type} -> (a -> b) -> Type
codomain _ = b

public export
typeOf : {a : Type} -> a -> Type
typeOf _ = a

