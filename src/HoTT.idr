module HoTT

import Basic
import Unit
import Void
import Coproduct
import Sigma
import Nat
import Path
import PreorderReasoning
import General
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

HomotopyRefl :
     {p : a -> Type}
  -> (f : (x : a) -> p x)
  -> f ~~ f
HomotopyRefl hom x = Refl (hom x)

HomotopySym :
     {p : a -> Type}
  -> {f, g : (x : a) -> p x}
  -> f ~~ g
  -> g ~~ f
HomotopySym hom x = sym (hom x)

||| This is also called horizontal composition.
HomotopyTransitive :
     {p : a -> Type}
  -> {f, g, h : (x : a) -> p x}
  -> f ~~ g
  -> g ~~ h
  -> f ~~ h
HomotopyTransitive alpha beta x =
  alpha x . beta x

HomotopyHorCompose :
     {p : a -> Type}
  -> {f, g, h : (x : a) -> p x}
  -> f ~~ g
  -> g ~~ h
  -> f ~~ h
HomotopyHorCompose = HomotopyTransitive

HomotopyVertCompose :
     {f, g : a -> b}
  -> {f', g' : b -> c}
  -> (f ~~ g)
  -> (f' ~~ g')
  -> (f . f') ~~ (g . g')
HomotopyVertCompose alpha beta x with (alpha x)
  HomotopyVertCompose alpha beta x | ax with (f x)
   HomotopyVertCompose alpha beta x | ax | fx with (g x)
    HomotopyVertCompose alpha beta x | Refl _ | fx | fx = beta fx

||| Non-dependent version
HomotopyNaturalTransformation :
     {f, g : a -> b}
  -> (hom : f ~~ g)
  -> (p : x == y)
  -> (hom x . ap g p) == (ap f p . hom y)
HomotopyNaturalTransformation hom (Refl x) =
  sym (ConcatRightNeutral (hom x)) . Refl (hom x) . ConcatLeftNeutral (hom x)

QInv :
     {a, b : _}
  -> (f : a -> b)
  -> Type
QInv f = Sigma (b -> a) \g => Pair (g . f ~~ id) (f . g ~~ id)

IsEquiv :
     {a, b : _}
  -> (f : a -> b)
  -> Type
IsEquiv f = Pair (Sigma (b -> a) \g => g . f ~~ id)
                 (Sigma (b -> a) \g => f . g ~~ id)

QInvIsEquiv :
     {f : a -> b}
  -> QInv f -> IsEquiv f
QInvIsEquiv (g # hom # hom') = (g # hom) # (g # hom')

EquivIsQInv :
     {a, b : _}
  -> {f : a -> b}
  -> IsEquiv f -> QInv f
EquivIsQInv ((g # alpha) # (h # beta)) =
  g # alpha # let
    alpha' = HomotopyVertCompose alpha (HomotopyRefl h)
    beta' = HomotopyVertCompose (HomotopyRefl g) beta
    gamma = HomotopyHorCompose (HomotopySym alpha') beta'
    gamma' = HomotopyVertCompose (HomotopyRefl f) gamma in
    HomotopyHorCompose (HomotopySym gamma') beta

infix 0 ~=

||| An equivalence from `a` to `b`.
(~=) : (a : Type) -> (b : Type) -> Type
a ~= b = Sigma (a -> b) IsEquiv

EquivalenceReflexive :
     (a : Type)
  -> a ~= a
EquivalenceReflexive a =
  id # (id # \x => Refl x) # (id # \x => Refl x)

EquivalenceSymmetric :
     {a, b : Type}
  -> a ~= b
  -> b ~= a
EquivalenceSymmetric (f # eq) =
  let (g # a # b) = EquivIsQInv {f} eq in g # QInvIsEquiv (f # b # a)
                 --              ^--- TODO Unifier should've actually solved that. Report ?

infixr 0 #
EquivalenceTransitive :
     {a, b, c : Type}
  -> a ~= b
  -> b ~= c
  -> a ~= c
EquivalenceTransitive (f # eqf) (g # eqg) =
  let (f' # a # b) = EquivIsQInv eqf
      (g' # c # d) = EquivIsQInv {f = g} eqg
                 --               ^--- TODO same problem
      alpha = HomotopyVertCompose (HomotopyRefl g') a
      alpha' = HomotopyVertCompose alpha (HomotopyRefl g)
      alpha'' = HomotopyHorCompose alpha' c
      beta = HomotopyVertCompose (HomotopyRefl f) d
      beta' = HomotopyVertCompose beta (HomotopyRefl f')
      beta'' = HomotopyHorCompose beta' b in
      f . g # QInvIsEquiv (g' . f' # alpha'' # beta'')

PairEqElim :
     {x, y : Pair a b}
  -> (p : x == y)
  -> Pair (pr1 x == pr1 y) (pr2 x == pr2 y)
PairEqElim p = ap pr1 p # ap pr2 p

PairEqIntro :
     {x, y : Pair a b}
  -> Pair (pr1 x == pr1 y) (pr2 x == pr2 y)
  -> x == y
PairEqIntro {x = e1 # e2, y = e1 # e2} (Refl _ # Refl _) =
  Refl (e1 # e2)

PairEqQInv : {a, b, x, y : _} -> QInv (PairEqElim {a, b, x, y})
PairEqQInv = PairEqIntro # fst # snd
 where
  fst : {a, b, x, y : _}
     -> (PairEqIntro {a, b, x, y} . PairEqElim {a, b, x, y})
     ~~ id {a = Pair (pr1 x == pr1 y) (pr2 x == pr2 y)}
  fst {x = e1 # e2, y = e1 # e2} (Refl _ # Refl _) = Refl (Refl e1 # Refl e2)

  snd : {a, b, x, y : _}
     -> (PairEqElim {a, b, x, y} . PairEqIntro {a, b, x, y})
     ~~ id {a = x == y}
  snd {x = e1 # e2, y = e1 # e2} (Refl _) = Refl (Refl (e1 # e2))

PairEqIsEquiv : {a, b, x, y : _} -> IsEquiv (PairEqElim {a, b, x, y})
PairEqIsEquiv = QInvIsEquiv PairEqQInv

PairUniqueness :
     (x : Pair a b)
  -> x == (pr1 {p = const b} x # pr2 {p = const b} x)
  -- TODO pretty strange why I had to manually specify the `p`.
PairUniqueness x =
  PairEqIntro {x} {y = pr1 x # pr2 x} (Refl (pr1 x) # Refl (pr2 x))


||| Product of type families.
namespace Family
  public export
  Cross :
       (a, b : ty -> Type)
    -> ty
    -> Type
  Cross a b x = Pair (a x) (b x)

TransportPair :
     {x, y : ty}
  -> {a, b : ty -> Type}
  -> (p : Id ty x y)
  -> (c : Pair (a x) (b x))
  -> transport (Cross a b) p c == (transport a p (pr1 c) # transport b p (pr2 c))
TransportPair (Refl x) c = PairUniqueness c

||| Product of functions.
namespace Function
  public export
  Cross :
       (f : a -> a')
    -> (g : b -> b')
    -> Pair a b -> Pair a' b'
  Cross f g x = f (pr1 x) # g (pr2 x)

ApFunctorialUnderPairEqLemma :
     (f : a -> a')
  -> (g : b -> b')
  -> (x, y : Pair a b)
  -> (p : pr1 x == pr1 y)
  -> (q : pr2 x == pr2 y)
  -> ap (Cross f g) (PairEqIntro {x, y} (p # q))
               --                 ^--^---TODO strange unification problems again
  == PairEqIntro (ap f p # ap g q)
ApFunctorialUnderPairEqLemma f g (a # b) (a # b) (Refl _) (Refl _) =
  Refl (Refl (f a # g b))

SigmaEqElim :
     {p : a -> Type}
  -> {w, w' : Sigma a p}
  -> (w == w')
  -> Sigma (pr1 w == pr1 w')
           (\path => transport p path (pr2 w) == pr2 w')
SigmaEqElim (Refl w) = Refl (pr1 w) # Refl (pr2 w)

SigmaEqIntro :
     {p : a -> Type}
  -> {w, w' : Sigma a p}
  -> Sigma (pr1 w == pr1 w')
           (\path => transport p path (pr2 w) == pr2 w')
  -> (w == w')
SigmaEqIntro {w = a # b, w' = a' # b'} sigma =
  SigmaInduction (\_ => Id (Sigma _ p) (a # b) (a' # b'))
    (\(Refl a) => \(Refl b) => Refl (a # b)) sigma

SigmaEqQInv :
     {p : a -> Type}
  -> {w, w' : Sigma a p}
  -> QInv (SigmaEqElim {p, w, w'})
SigmaEqQInv {w = a # b, w' = a' # b'} =
  SigmaEqIntro # (\(Refl _ # Refl _) => Refl (Refl a # Refl b))
               # (\(Refl (a # b)) => Refl (Refl (a # b)))

SigmaEqIsEquiv :
     {p : a -> Type}
  -> {w, w' : Sigma a p}
  -> IsEquiv (SigmaEqElim {p, w, w'})
SigmaEqIsEquiv =
  QInvIsEquiv {f = SigmaEqElim {p, w, w'}}
              (SigmaEqQInv {p, w, w'})

SigmaUniqueness :
     {p : a -> Type}
  -> (z : Sigma a p)
  -> z == (pr1 z # pr2 z)
SigmaUniqueness z =
  SigmaEqIntro {w = z, w' = pr1 z # pr2 z} (Refl (pr1 z) # Refl (pr2 z))

UnitEqElim :
     {x, y : Unit}
  -> (x == y)
  -> Unit
UnitEqElim _ = MkUnit

UnitEqIntro :
     {x, y : Unit}
  -> Unit
  -> (x == y)
UnitEqIntro {x = MkUnit, y = MkUnit} _ = Refl MkUnit

UnitEqQInv : {x, y : Unit} -> QInv (UnitEqElim {x, y})
UnitEqQInv = UnitEqIntro
           # (\MkUnit => Refl MkUnit)
           # (\(Refl MkUnit) => Refl (Refl MkUnit))

UnitEqIsEquiv : {x, y : Unit} -> IsEquiv (UnitEqElim {x, y})
UnitEqIsEquiv = QInvIsEquiv {f = UnitEqElim} (UnitEqQInv {x, y})

UnitUniqueness : (z : Unit) -> z == MkUnit
UnitUniqueness z = UnitEqIntro {x = z, y = MkUnit} MkUnit

EquivUniqueness :
    (f : a -> b)
 -> (e1, e2 : IsEquiv f)
 -> e1 == e2
-- e : g . f ~~ id
-- q : h . f ~~ id

-- e' : f . g' ~~ id
-- q' : f . h' ~~ id

-- ? :
EquivUniqueness f ((g # e) # (g' # e')) ((h # q) # (h' # q')) =
  PairEqIntro (?a # ?b)

