module General

import Basic
import Unit
import Void
import Sigma
import Coproduct
import Path
import PreorderReasoning

infix 0 <=>

||| Logical equivalence
public export
(<=>) : Type -> Type -> Type
a <=> b = Pair (a -> b) (b -> a)

infix 0 ~~

||| Pointwise equality of functions.
||| A homotopy from f to g.
public export
(~~) : {p : a -> Type} -> (f, g : (x : a) -> p x) -> Type
f ~~ g = (x : a) -> f x == g x

infix 0 /=

public export
(/=) : a -> a -> Type
x /= y = Neg (x == y)

public export
negSym : {x, y : _} -> x /= y -> y /= x
negSym p u = p (sym u)

