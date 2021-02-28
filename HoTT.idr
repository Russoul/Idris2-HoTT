module HoTT

import Basic
import Unit
import Void
import Coproduct
import Sigma
import Nat
import Path
import PreorderReasoning
import Dec

%default total

-- Little nuances and inconveniences experienced while writing this:
-- 1)Not overloadable syntax: = (,) ()
--  and, in general, no custom syntax extensions.
-- 2)Why prefix (-) is parsed as `negate` ?
-- 3)Lexicographically ordered fixities over Natural Numbers ?
--   It solves the problem:
--   For any two fixities x, z such that x < z
--     there is a fixity y such that x < y < z
--     (and x, y, z are Natural Numbers, which is convenient).
-- 4)No option to unhide global names.
-- 5)System of numeric literal overloading is flawed:
--    Overloading of numeric literals works by providing a function of type `Integer -> a`.
--    But to carry this out for naturals
--     we have to map all negative integers to zero in this case, to provide a sensible transformation.


-- The project doesn't depend on the Prelude and other libraries
-- to be bare-bones and more comprehensible

-- Some operators and names are chosen to be different
-- from the standard ones to closely follow those found in
-- the HoTT book or in this course: https://arxiv.org/pdf/1911.00580.pdf

-- While sometimes differing naming is introduced as a matter of preference.


-- TODO Univalent TT

IsCenter : (a : Type) -> a -> Type
IsCenter a c = (x : a) -> c == x

IsSingleton : Type -> Type
IsSingleton a = Sigma a (\c => IsCenter a c)

UnitIsSingleton : IsSingleton Unit
UnitIsSingleton = () # UnitInduction (\x => () == x) (Refl ())

Center : (a : Type) -> IsSingleton a -> a
Center _ (x # _) = x

Centrality : (a : Type) -> (i : IsSingleton a) -> (x : a) -> Center a i == x
Centrality _ (_ # phi) = phi

IsSubsingleton : Type -> Type
IsSubsingleton a = (x, y : a) -> x == y

-------------------

LoopSpace : (ty : Type) -> (a : ty) -> Type
LoopSpace ty a = Id ty a a

Omega1 : (ty : Type) -> (a : ty) -> Type
Omega1 = LoopSpace

-- LoopSpace forms a higher group

Omega2 : (ty : Type) -> (a : ty) -> Type
Omega2 ty a = Id (Id ty a a) (Refl a) (Refl a)

ConcatRightNeutral : (p : Id ty a b)
                   -> p == (p . Refl b)
ConcatRightNeutral (Refl b) = Refl (Refl b)

ConcatLeftNeutral : (p : Id ty a b)
                 -> p == (Refl a . p)
ConcatLeftNeutral (Refl b) = Refl (Refl b)

ConcatLeftIdentity : (p : Id ty a b)
                   -> (sym p . p) == Refl b
ConcatLeftIdentity (Refl b) = Refl (Refl b)

ConcatRightIdentity : (p : Id ty a b)
                   -> (p . sym p) == Refl a
ConcatRightIdentity (Refl a) = Refl (Refl a)

SymIdempotent : (p : Id ty a b)
             -> (p == sym (sym p))
SymIdempotent (Refl b) = Refl (Refl b)

ConcatAssoc : (p : Id ty a b)
           -> (q : Id ty b c)
           -> (r : Id ty c d)
           -> (p . (q . r)) == ((p . q) . r)
ConcatAssoc (Refl b) (Refl b) (Refl b) = Refl (Refl b)

RightWhisker : (a, b, c : ty)
            -> (p, q : Id ty a b)
            -> (alpha : Id (Id ty a b) p q)
            -> (r : Id ty b c)
            -> Id (Id ty a c) (p . r) (q . r)
RightWhisker a b b p q alpha (Refl b) =
  sym (ConcatRightNeutral p) . alpha . ConcatRightNeutral q

LeftWhisker : (a, b, c : ty)
           -> (q : Id ty a b)
           -> (r, s : Id ty b c)
           -> (beta : Id (Id ty b c) r s)
           -> Id (Id ty a c) (q . r) (q . s)
LeftWhisker b b c (Refl b) r s beta =
  sym (ConcatLeftNeutral r) . beta . ConcatLeftNeutral s

HorizontalComposition : (a, b, c : ty)
                    -> (p, q : Id ty a b)
                    -> (r, s : Id ty b c)
                    -> (alpha : Id (Id ty a b) p q)
                    -> (beta : Id (Id ty b c) r s)
                    -> Id (Id ty a c) (p . r) (q . s)
HorizontalComposition a b c p q r s alpha beta =
  RightWhisker a b c p q alpha r . LeftWhisker a b c q r s beta

HorizontalComposition' : (a, b, c : ty)
                     -> (p, q : Id ty a b)
                     -> (r, s : Id ty b c)
                     -> (alpha : Id (Id ty a b) p q)
                     -> (beta : Id (Id ty b c) r s)
                     -> Id (Id ty a c) (p . r) (q . s)
HorizontalComposition' a b c p q r s alpha beta =
  LeftWhisker a b c p r s beta . RightWhisker a b c p q alpha s

HorizontalCompositionsAgree :
     (a, b, c : ty)
  -> (p, q : Id ty a b)
  -> (r, s : Id ty b c)
  -> (alpha : Id (Id ty a b) p q)
  -> (beta : Id (Id ty b c) r s)
  -> HorizontalComposition a b c p q r s alpha beta
  == HorizontalComposition' a b c p q r s alpha beta
HorizontalCompositionsAgree b b b
  (Refl b) (Refl b) (Refl b)
  (Refl b) (Refl (Refl b)) (Refl (Refl b)) =
    Refl (Refl (Refl b))

Omega2HorizontalCompose :
     (alpha, beta : Omega2 ty a)
  -> (alpha . beta)
  == HorizontalComposition a a a (Refl a) (Refl a) (Refl a) (Refl a)
       alpha beta
Omega2HorizontalCompose (Refl (Refl a)) (Refl (Refl a)) =
  Refl (Refl (Refl a))

-- Eckmann-Hilton
Omega2ConcatCommut : (alpha, beta : Omega2 ty a)
                  -> (alpha . beta) == (beta . alpha)
Omega2ConcatCommut (Refl (Refl a)) (Refl (Refl a)) =
  Refl (Refl (Refl a))
