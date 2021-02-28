module CoproductProps

import Basic
import Unit
import Void
import Coproduct

import Path
import General
import Dec

public export
UnitNotVoid : Unit /= Void
UnitNotVoid p = IdFun p ()

public export
-- p : 1 == 0
OneNotTwo : Inr () /= Inl ()
OneNotTwo p = UnitNotVoid q
 where
  f : Two -> Type
  f (Inl ()) = Void
  f (Inr ()) = Unit

  q : Unit == Void
  q = ap f p

public export
TwoDecEq : DecEq Two
-- 0 == 0 + Neg (0 == 0)
TwoDecEq (Inl ()) (Inl ()) = Inl (Refl (Inl ()))
-- (0 == 1) + Neg (0 == 1)
TwoDecEq (Inl ()) (Inr ()) = Inr (negSym OneNotTwo)
-- (1 == 0) + Neg (1 == 0)
TwoDecEq (Inr ()) (Inl ()) = Inr OneNotTwo
-- 1 == 1 + Neg (1 == 1)
TwoDecEq (Inr ()) (Inr ()) = Inl (Refl (Inr ()))

public export
NotZeroIsOne : (n : Two) -> n /= Inl () -> n == Inr ()
-- 0 /= 0
NotZeroIsOne (Inl ()) f = VoidInduction
  (const $ Inl () == Inr ()) (f (Refl _))
-- 1 /= 0 -> 1 == 1
NotZeroIsOne (Inr ()) f = Refl _

public export
SumDisjointImages : {x : a} -> {y : b} -> Inl x /= Inr y
SumDisjointImages p = UnitNotVoid q
-- p : 0 == 1
 where
  f : a + b -> Type
  f (Inl x) = Unit
  f (Inr y) = Void

  q : Unit == Void
  q = ap f p

public export
LeftIfNotRight : a + b -> Neg b -> a
LeftIfNotRight (Inl p) _ = p
LeftIfNotRight (Inr p) f = VoidRecursion a (f p)
