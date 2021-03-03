module Sigma

import Basic
import Unit
import Void

infixr 0 #
public export
data Sigma : (a : Type) -> (p : a -> Type) -> Type where
  (#) : (x : a) -> p x -> Sigma a p

public export
Pair : Type -> Type -> Type
Pair a b = Sigma a (const b)

public export
pr1 : Sigma a p -> a
pr1 (x # _) = x

public export
pr2 : (s : Sigma a p) -> p (pr1 s)
pr2 (_ # y) = y

public export
SigmaInduction : (q : Sigma a p -> Type)
              -> ((x : a) -> (y : p x) -> q (x # y))
              -> (s : Sigma a p) -> q s
SigmaInduction _ f (x # y) = f x y

public export
uncurry : (q : Sigma a p -> Type)
       -> ((x : a) -> (y : p x) -> q (x # y))
       -> (s : Sigma a p) -> q s
uncurry = SigmaInduction

public export
curry : (q : Sigma a p -> Type)
     -> ((s : Sigma a p) -> q s)
     -> ((x : a) -> (y : p x) -> q (x # y))
curry _ f x y = f (x # y)

