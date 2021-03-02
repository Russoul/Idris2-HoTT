module Coproduct

import Basic
import Unit
import Void

%default total

infixl 5 +

namespace Coproduct
  public export
  data (+) : Type -> Type -> Type where
   Inl : a -> a + b
   Inr : b -> a + b

public export
SumInduction : (p : a + b -> Type)
            -> ((x : a) -> p (Inl x))
            -> ((y : b) -> p (Inr y))
            -> (z : a + b) -> p z
SumInduction p f g (Inl x) = f x
SumInduction p f g (Inr y) = g y

public export
SumRecursion : (p : Type)
            -> ((x : a) -> p)
            -> ((y : b) -> p)
            -> (z : a + b) -> p
SumRecursion p = SumInduction (const p)

public export
Two : Type
Two = Unit + Unit

public export
TwoInduction : (p : Two -> Type)
            -> p (Inl ())
            -> p (Inr ())
            -> (two : Two) -> p two
TwoInduction p pl pr = SumInduction p
  (UnitInduction (p `compose` Inl) pl) (UnitInduction (p `compose` Inr) pr)

