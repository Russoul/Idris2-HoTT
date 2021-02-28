module NatProps

import Basic
import Unit
import Void
import Coproduct
import Nat
import Sigma
import Path
import CoproductProps
import PreorderReasoning
import General
import Dec

%default total

NegN : (n : Nat) -> Type -> Type
NegN Z p = p
NegN (S k) p = Neg (NegN k p)

dni : p -> NegN N.two p
dni a u = u a

contrapositive : (a -> b) -> (Neg b -> Neg a)
contrapositive f v a = v (f a)

tno : NegN N.three p -> Neg p
tno = contrapositive dni

absurdityX3IsAbsurdity : {p : _} -> NegN N.three p <=> Neg p
absurdityX3IsAbsurdity = firstly # secondly
 where
  firstly : NegN N.three p -> Neg p
  firstly = tno

  secondly : Neg p -> NegN N.three p
  secondly = dni

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

||| Alternative definition of non-strict inequality.
Lte' : Nat -> Nat -> Type
Lte' x y = Sigma Nat (\z => z + x == y)

LteImpliesLte' : (x, y : Nat) -> x <= y -> Lte' x y
LteImpliesLte' Z y _ = y # (Chain $ ||  y + Z
                                    |=> Z + y ...(PlusComm y Z))
LteImpliesLte' (S _) Z l = VoidRecursion _ l
-- prf  : z + x == y
-- goal : z + S x == S y
LteImpliesLte' (S x) (S y) l = let z # prf = LteImpliesLte' x y l in
  let prf' = Chain $ ||     z +   x ==   y
                      |=>   x +   z ==   y ...(OnLhs $ PlusComm z x)
                      |=> S x +   z == S y ...(ap S)
                      |=>   z + S x == S y ...(OnLhs $ PlusComm (S x) z)
                   $ prf
  in  z # prf'

Lte'ImpliesLte : (x, y : Nat) -> Lte' x y -> x <= y
Lte'ImpliesLte Z _ _ = ()
Lte'ImpliesLte (S x) Z (z # contra) =
  let contra' = OnLhs (PlusComm z (S x)) contra in
  let p = PositiveNotZero (x + z) in
  p contra'
Lte'ImpliesLte (S x) (S y) (z # prf) =
  let prf' = Chain $ ||  z + S x == S y
                     |=> S x + z == S y ...(OnLhs $ PlusComm z (S x))
                     |=> x + z == y ...(ap pred)
                     |=> z + x == y ...(OnLhs $ PlusComm x z)
                   $ prf in
  Lte'ImpliesLte x y (z # prf')

LogicallyEqualivalentLte : (x, y : Nat) -> x <= y <=> Lte' x y
LogicallyEqualivalentLte x y = LteImpliesLte' x y
                             # Lte'ImpliesLte x y

LteRefl : (n : Nat) -> n <= n
LteRefl Z = ()
LteRefl (S n) = LteRefl n

LteTrans : (l, m, n : Nat) -> l <= m -> m <= n -> l <= n
LteTrans Z m n q p = ()
LteTrans (S l) Z n q p = VoidRecursion _ q
LteTrans (S l) (S m) Z q p = VoidRecursion _ p
LteTrans (S l) (S m) (S n) q p = LteTrans l m n q p

LteAnti : (m, n : Nat) -> m <= n -> n <= m -> m == n
LteAnti Z Z q p = Refl Z
LteAnti (S m) Z q p = VoidRecursion _ q
LteAnti Z (S n) q p = VoidRecursion _ p
LteAnti (S m) (S n) q p = ap S $ LteAnti m n q p

LteSucc : (n : Nat) -> n <= S n
LteSucc Z = ()
LteSucc (S n) = LteSucc n

ZeroMinimal : (n : Nat) -> Z <= n
ZeroMinimal _ = ()

UniqueMinimal : (n : Nat) -> n <= Z -> n == Z
UniqueMinimal Z p = Refl Z
UniqueMinimal (S n) p = VoidRecursion _ p

LteSplit : (m, n : Nat) -> m <= S n -> (m <= n) + (m == S n)
LteSplit Z n p = Inl ()
LteSplit (S m) Z p with (UniqueMinimal _ p)
 LteSplit (S Z) Z p | Refl _ = Inr (Refl (S Z))
LteSplit (S m) (S n) p = let H = LteSplit m n p in
  case H of
    Inl p => Inl p
    Inr p => Inr (ap S p)

LteSplit' : (m, n : Nat) -> m <= n -> (S m <= n) + (m == n)
LteSplit' Z Z p = Inr (Refl Z)
LteSplit' Z (S n) p = Inl ()
LteSplit' (S m) Z p = VoidRecursion _ p
LteSplit' (S m) (S n) p =
  case LteSplit' m n p of
    Inl x => Inl x
    Inr x => Inr (ap S x)


infixl 1 <

(<) : Nat -> Nat -> Type
x < y = S x <= y

NotLtGivesLte : (m, n : Nat) -> Neg (n < m) -> m <= n
NotLtGivesLte Z n _ = ()
NotLtGivesLte (S m) Z p = p ()
NotLtGivesLte (S m) (S n) p = NotLtGivesLte m n p

BoundedForallNext : (p : Nat -> Type)
                 -> (k : Nat)
                 -> p k
                 -> ((n : Nat) -> n < k -> p n)
                 -> (n : Nat) -> n < S k -> p n
BoundedForallNext p k pk f n l with (LteSplit' n k l)
 BoundedForallNext p k pk f n l | Inl prf = f n prf
 BoundedForallNext p k pk f k l | Inr (Refl _) = pk

||| The type of roots of a function.
Root : (Nat -> Nat) -> Type
Root f = Sigma Nat (\n => f n == Z)

HasNoRootLt : (Nat -> Nat) -> Nat -> Type
HasNoRootLt f k = (n : Nat) -> n < k -> f n /= Z

IsMinimalRoot : (Nat -> Nat) -> Nat -> Type
IsMinimalRoot f m = Pair (f m == Z) (f `HasNoRootLt` m)

AtMostOneMinimalRoot : (f : Nat -> Nat)
                    -> (m, n : Nat)
                    -> IsMinimalRoot f m
                    -> IsMinimalRoot f n
                    -> m == n
-- prfm : forall n. n < m -> f n == Z -> Void
-- prfn : forall m. m < n -> f m == Z -> Void
AtMostOneMinimalRoot f m n (rm # prfm) (rn # prfn) = c _ _ a b
 where
  a : Neg (m < n)
  a contra = prfn m contra rm

  b : Neg (n < m)
  b contra = prfm n contra rn

  c : (m, n : Nat) -> Neg (m < n) -> Neg (n < m) -> m == n
  c m n q q' = LteAnti m n (NotLtGivesLte _ _ q') (NotLtGivesLte _ _ q)

MinimalRoot : (Nat -> Nat) -> Type
MinimalRoot f = Sigma Nat (IsMinimalRoot f)

MinimalRootIsRoot : MinimalRoot f -> Root f
MinimalRootIsRoot (r # prf # _) = r # prf

BoundedNatSearch : (k, f : _) -> MinimalRoot f + (f `HasNoRootLt` k)
BoundedNatSearch Z f = Inr (\_, v, _ => v)
BoundedNatSearch (S k) f = SumRecursion _ Inl y
  (BoundedNatSearch k f)
 where
  A : Nat -> (Nat -> Nat) -> Type
  A k f = MinimalRoot f + (f `HasNoRootLt` k)

  y : f `HasNoRootLt` k -> A (S k) f
  y u = SumRecursion _ y0 y1 (NatDecEq (f k) Z)
   where
    y0 : f k == Z -> A (S k) f
    y0 p = Inl (k # p # u)

    y1 : f k /= Z -> A (S k) f
    y1 v = Inr (BoundedForallNext (\n => f n /= Z) k v u)

RightFailsGivesLeftHolds : {P, Q : Type} -> P + Q -> Neg Q -> P
RightFailsGivesLeftHolds (Inl p) u = p
RightFailsGivesLeftHolds (Inr q) u = VoidRecursion _ (u q)

RootGivesMinimalRoot : (f : _) -> Root f -> MinimalRoot f
RootGivesMinimalRoot f (n # p) = y
 where
  g : Neg (f `HasNoRootLt` S n)
  g phi = phi n (LteRefl n) p

  y : MinimalRoot f
  y = RightFailsGivesLeftHolds (BoundedNatSearch (S n) f) g

