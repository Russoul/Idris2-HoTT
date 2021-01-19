module HoTT

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
-- 5)No way to overload natural number literals without depending
--   on Prelude
-- 6)System of numeric literal overloading is flawed:
--    overloading numeric literals works by providing a function of type `Integer -> a`
--    but we have to map all negative integers to zero in this case, to provide a sensible transformation.


-- The project doesn't depend on the Prelude and other libraries
-- to be bare-bones and more comprehensible

-- Some operators and names are chosen to be different
-- from the standard ones to closely follow those found in
-- the HoTT book or in this course: https://arxiv.org/pdf/1911.00580.pdf

-- While sometimes differing naming is introduced as a matter of preference.

infixl 0 $

%inline public export
($) : (a -> b) -> a -> b
($) f x = f x

the : (a : Type) -> (x : a) -> a
the _ x = x

id : a -> a
id x = x

const : a -> b -> a
const x _ = x

infixl 1 .

(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

data Unit : Type where
  MkUnit : Unit

UnitInduction : (p : Unit -> Type) -> p () -> (x : Unit) -> p x
UnitInduction _ prop () = prop

UnitRecursion : (p : Type) -> p -> Unit -> p
UnitRecursion _ p () = p

UnitTerminal : (p : Type) -> p -> Unit
UnitTerminal _ = const ()

data Void : Type where

VoidInduction : (0 p : Void -> Type) -> (0 x : Void) -> p x
VoidInduction _ x impossible

VoidRecursion : (0 p : Type) -> (0 x : Void) -> p
VoidRecursion p = VoidInduction (const p)

VoidInitial : (0 p : Type) -> (0 x : Void) -> p
VoidInitial = VoidRecursion

IsEmpty : Type -> Type
IsEmpty a = a -> Void

Neg : Type -> Type
Neg = IsEmpty

data Nat = Z | S Nat

NatInduction : (p : Nat -> Type)
            -> p Z
            -> ((n : Nat) -> p n -> p (S n))
            -> (n : Nat) -> p n
NatInduction _ p0 pn Z = p0
NatInduction p p0 pn (S n) = pn n (NatInduction p p0 pn n)

NatRecursion : (p : Type) -> p -> (Nat -> p -> p) -> Nat -> p
NatRecursion p = NatInduction (const p)

NatIteration : (p : Type) -> p -> (p -> p) -> Nat -> p
NatIteration p p0 f = NatRecursion p p0 (const f)

infixl 5 +
infixl 6 *

(+) : Nat -> Nat -> Nat
Z + k = k
(S n) + k = S (n + k)

(*) : Nat -> Nat -> Nat
Z * k = Z
(S n) * k = k + n * k

infixl 1 <=
infixl 1 >=

namespace NatOrder
  public export
  (<=) : Nat -> Nat -> Type
  Z   <= _   = Unit
  S n <= Z   = Void
  S n <= S k = n <= k

  public export
  (>=) : Nat -> Nat -> Type
  n >= k = Neg (n <= k)

namespace SumType
  public export
  data (+) : Type -> Type -> Type where
   Inl : a -> a + b
   Inr : b -> a + b

SumInduction : (p : a + b -> Type)
            -> ((x : a) -> p (Inl x))
            -> ((y : b) -> p (Inr y))
            -> (z : a + b) -> p z
SumInduction p f g (Inl x) = f x
SumInduction p f g (Inr y) = g y

Two : Type
Two = Unit + Unit

TwoInduction : (p : Two -> Type)
            -> p (Inl ())
            -> p (Inr ())
            -> (two : Two) -> p two
TwoInduction p pl pr = SumInduction p
  (UnitInduction (p . Inl) pl) (UnitInduction (p . Inr) pr)

infixr 20 #
data Sigma : (a : Type) -> (p : a -> Type) -> Type where
  (#) : (x : a) -> p x -> Sigma a p

Pair : Type -> Type -> Type
Pair a b = Sigma a (const b)

pr1 : Sigma a p -> a
pr1 (x # _) = x

pr2 : (s : Sigma a p) -> p (pr1 s)
pr2 (_ # y) = y

SigmaInduction : (q : Sigma a p -> Type)
              -> ((x : a) -> (y : p x) -> q (x # y))
              -> (s : Sigma a p) -> q s
SigmaInduction _ f (x # y) = f x y

curry : (q : Sigma a p -> Type)
     -> ((s : Sigma a p) -> q s)
     -> ((x : a) -> (y : p x) -> q (x # y))
curry _ f x y = f (x # y)

domain : {a : Type} -> (a -> b) -> Type
domain _ = a

codomain : {b : Type} -> (a -> b) -> Type
codomain _ = b

typeOf : {a : Type} -> a -> Type
typeOf _ = a

||| Type of identities or paths between elements of types or points in topological spaces.
data Id : (0 a : Type) -> a -> a -> Type where
  Refl : (x : a) -> Id a x x

infix 4 ==

(==) : a -> a -> Type
x == y = Id _ x y

||| Induction principle for paths
J : (p : (x, y : a) -> (x == y) -> Type)
 -> ((x : a) -> p x x (Refl x))
 -> (x, y : a) -> (i : x == y) -> p x y i
J p f x x (Refl x) = f x

-- Another one
H : (x : a) -> (p : (y : a) -> (x == y) -> Type)
 -> p x (Refl x)
 -> (y : a) -> (i : x == y) -> p y i
H x p f x (Refl x) = f

-- J and H agree (no proof here)
-- TODO prove it ?

-- No axiom-K

-- Axiom-K is incompatible with the Univalence Axiom.
-- But unfortunately the former is provable in Idris 2.
-- And there is no option to remove it from the system.

-- In practice this means that we must not pattern match
-- on loops (paths from a point to itself)
-- i.e

-- veryBad : x === x -> ...
-- veryBad Refl = ...

-- but on the other hand, this is ok:
-- noContradiction : x === y -> ...
-- noContradiction Refl = ...

transport : (p : a -> Type) -> {x, y : _} -> x == y -> p x -> p y
transport p i = J (\x, y, _ => p x -> p y) (\_ => id) _ _ i

namespace Id
  public export
  (.) : {x, y, z : a} -> x == y -> y == z -> x == z
  p . q = transport (x ==) q p

infixl 2  |=>
prefix 3  ||
infix  3  ...

||| Reason about paths/identities transitively.
||| Start at Reflexivity.
namespace PreorderReasoningPath
  public export
  data StepP : a -> b -> Type where
    (...) : (0 y : a) -> (0 step : x == y) -> StepP x y

  public export
  data DeriveP : (x : a) -> (y : b) -> Type where
    (||) : (0 x : a) -> DeriveP x x
    (|=>) : DeriveP x y -> {0 z : a} -> (step : StepP y z) -> DeriveP x z

  public export
  Chain : {x, y : a} -> DeriveP x y -> x == y
  Chain (|| x) = Refl x
  Chain ((|=>) der (_ ... Refl _)) = Chain der

||| Reason about functions transitively.
||| Start at Identity.
namespace PreorderReasoningFunction
  public export
  data StepF : a -> b -> Type where
    (...) : (b : Type) -> (f : a -> b) -> StepF a b

  public export
  data DeriveF : a -> b -> Type where
    (||) : (a : Type) -> DeriveF a a
    (|=>) : DeriveF a b
         -> StepF b c
         -> DeriveF a c

  public export
  Chain : DeriveF a b -> a -> b
  Chain (|| _) = id
  Chain (p |=> (_ ... f)) = f . Chain p

||| p <=> p⁻¹
sym : {x, y : a} -> (p : x == y) -> y == x
sym p = transport (== x) p (Refl x)

||| Congurence or f(p) in HoTT book
||| p => f(p)
ap : {x, y : a} -> (f : a -> b) -> (p : x == y) -> f x == f y
ap f p = transport (\that => f x == f that) p (Refl (f x))

infix 0 ~~

||| Pointwise equality of functions
(~~) : {x, y : _} -> {p : a -> Type} -> (f, g : (x : a) -> p x) -> Type
f ~~ g = (x : a) -> f x == g x

NegN : (n : Nat) -> Type -> Type
NegN Z p = p
NegN (S k) p = Neg (NegN k p)

namespace N
  %inline public export
  zero : Nat
  zero = Z

  %inline public export
  one : Nat
  one = S zero

  %inline public export
  two : Nat
  two = S one

  %inline public export
  three : Nat
  three = S two

  %inline public export
  four : Nat
  four = S three

dni : p -> NegN N.two p
dni a u = u a

contrapositive : (a -> b) -> (Neg b -> Neg a)
contrapositive f v a = v (f a)

tno : NegN N.three p -> Neg p
tno = contrapositive HoTT.dni

infix 0 <=>

||| Logical equivalence
(<=>) : Type -> Type -> Type
a <=> b = Pair (a -> b) (b -> a)

absurdityX3IsAbsurdity : {p : _} -> NegN N.three p <=> Neg p
absurdityX3IsAbsurdity = firstly # secondly
 where
  firstly : NegN N.three p -> Neg p
  firstly = HoTT.tno

  secondly : Neg p -> NegN N.three p
  secondly = dni

infix 0 /=

(/=) : a -> a -> Type
x /= y = Neg (x == y)

negSym : {x, y : _} -> x /= y -> y /= x
negSym p u = p (sym u)

IdFun : {a, b: Type} -> a == b -> a -> b
IdFun = transport id

UnitNotVoid : Unit /= Void
UnitNotVoid p = IdFun p ()

-- p : 1 == 0
OneNotTwo : Inr () /= Inl ()
OneNotTwo p = UnitNotVoid q
 where
  f : Two -> Type
  f (Inl ()) = Void
  f (Inr ()) = Unit

  q : Unit == Void
  q = ap f p

Dec : Type -> Type
Dec a = a + Neg a

DecEq : Type -> Type
DecEq a = (x, y : a) -> Dec (x == y)

TwoDecEq : DecEq Two
-- 0 == 0 + Neg (0 == 0)
TwoDecEq (Inl ()) (Inl ()) = Inl (Refl (Inl ()))
-- (0 == 1) + Neg (0 == 1)
TwoDecEq (Inl ()) (Inr ()) = Inr (negSym OneNotTwo)
-- (1 == 0) + Neg (1 == 0)
TwoDecEq (Inr ()) (Inl ()) = Inr OneNotTwo
-- 1 == 1 + Neg (1 == 1)
TwoDecEq (Inr ()) (Inr ()) = Inl (Refl (Inr ()))

NotZeroIsOne : (n : Two) -> n /= Inl () -> n == Inr ()
-- 0 /= 0
NotZeroIsOne (Inl ()) f = VoidInduction
  (const $ Inl () == Inr ()) (f (Refl _))
-- 1 /= 0 -> 1 == 1
NotZeroIsOne (Inr ()) f = Refl _

SumDisjointImages : {x : a} -> {y : b} -> Inl x /= Inr y
SumDisjointImages p = UnitNotVoid q
-- p : 0 == 1
 where
  f : a + b -> Type
  f (Inl x) = Unit
  f (Inr y) = Void

  q : Unit == Void
  q = ap f p

LeftIfNotRight : a + b -> Neg b -> a
LeftIfNotRight (Inl p) _ = p
LeftIfNotRight (Inr p) f = VoidRecursion a (f p)

PositiveNotZero : (x : Nat) -> S x /= Z
-- p : S x == Z
PositiveNotZero x p = UnitNotVoid (g p)
 where
  f : Nat -> Type
  f Z = Void
  f (S _) = Unit

  g : S x == Z -> Unit == Void
  g = ap f

pred : Nat -> Nat
pred Z = Z
pred (S k) = k

SuccLeftCancel : {x, y : _} -> S x == S y -> x == y
SuccLeftCancel = ap pred

NatNotSuccNat : (x : Nat) -> x /= S x
NatNotSuccNat Z = negSym (PositiveNotZero Z)
NatNotSuccNat (S k) = let r = NatNotSuccNat k in \l =>
  r (SuccLeftCancel l)

-- Proof that Nat has decidable equality.
-- Doesn't use pattern matching.
-- OMG
-- You'll never know the true value of pattern matching
-- until you are left without it (as an exercise).
namespace NatDec
  Lemma0 : {x, y : _} -> x == y -> (S x /= y)
  Lemma0 p = J (\x, y, _ => (S x /= y))
    (\x => negSym (NatNotSuccNat x)) x y p

  Lemma1 : {x, y : _} -> Dec (x == y) -> Dec (S x == S y)
  Lemma1 = SumInduction (const $ Dec (S x == S y))
    (\p => Inl (ap S p))
    (\p => Inr (\l => p (SuccLeftCancel l)))

  export
  NatDecEq : DecEq Nat
  NatDecEq x y = NatInduction (\x => (y : Nat) -> (x == y) + (x /= y))
    -- p0 : (y : Nat) -> (Z == y) + (Z /= y)
    (\y => (NatInduction (\y => (Z == y) + (Z /= y))
      -- p0
      (Inl $ Refl Z)
      -- pn
      (\y, _ => Inr (negSym $ PositiveNotZero y))
      --n
      y))
    -- pn : (x : Nat) -> (y : Nat) -> (S x == y) + (S x /= y)
    -- hyp : Dec (x == y)
    (\x, hyp, y =>
      NatInduction (\y => (S x == y) + (S x /= y))
        --p0
        (Inr (PositiveNotZero x))
        --pn
        (\y, _ => Lemma1 $ hyp y)
        --n
        y)
    x y

plusAssoc : (x, y, z : Nat) -> (x + y) + z == x + (y + z)
plusAssoc  Z    y z = Chain $ ||  (Z + y) + z
                             |=> Z + (y + z)     ...(Refl _)
plusAssoc (S x) y z = Chain $ ||  (S x + y) + z
                             |=> S ((x + y) + z) ...(Refl _)
                             |=> S (x + (y + z)) ...(ap S $ plusAssoc x y z)
                             |=> (S x + (y + z)) ...(Refl _)

BaseOnRight : (x : Nat) -> x + Z == x
BaseOnRight Z = Refl _
BaseOnRight (S x) = ap S (BaseOnRight x)

StepOnRight : (x, y : Nat) -> x + S y == S (x + y)
-- goal : S y == S (Z + y)
StepOnRight Z y = Refl _
-- goal : S (x + S y) == S (S (x + y))
StepOnRight (S x) y = Chain $ ||  S (x + S y)
                             |=> S (S (x + y)) ...(ap S $ StepOnRight x y)

PlusComm : (x, y : Nat) -> x + y == y + x
PlusComm x Z = BaseOnRight x
-- goal : x + S y == S (y + x)
PlusComm x (S y) = Chain $ ||  x + S y
                          |=> S (x + y) ...(StepOnRight x y)
                          |=> S (y + x) ...(ap S $ PlusComm x y)

OnLhs : {x, y, z : _} -> x == z -> x == y -> z == y
OnLhs p q = sym p . q

OnRhs : {x, y, z : _} -> y == z -> x == y -> x == z
OnRhs p q = q . p

PlusRightCancel : (x, y, z : Nat) -> x + y == z + y -> x == z
-- goal : x == z
-- prf  : x + Z == z + Z
PlusRightCancel x Z z prf = Chain $ ||  x
                                   |=> x + Z   ...(sym $ BaseOnRight x)
                                   |=> z + Z   ...prf
                                   |=> z       ...(BaseOnRight z)
-- goal : x == z
-- prf : x + S y == z + S y
-- prf' : TypeOf prf -> x + y == z + y
-- hyp : x + y == z + y -> x == z
PlusRightCancel x (S y) z prf =
  let prf' =
    Chain $ ||  x + S y == z + S y
            |=> S (x + y) == z + S y   ...(OnLhs $ StepOnRight x y)
            |=> S (x + y) == S (z + y) ...(OnRhs $ StepOnRight z y)
            |=> x + y == z + y         ...SuccLeftCancel
          $
            prf
  in PlusRightCancel x y z prf'

