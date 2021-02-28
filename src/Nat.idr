module Nat

import Basic
import Unit
import Void

public export
data Nat = Z | S Nat

public export
NatInduction : (p : Nat -> Type)
            -> p Z
            -> ((n : Nat) -> p n -> p (S n))
            -> (n : Nat) -> p n
NatInduction _ p0 pn Z = p0
NatInduction p p0 pn (S n) = pn n (NatInduction p p0 pn n)

public export
NatRecursion : (p : Type) -> p -> (Nat -> p -> p) -> Nat -> p
NatRecursion p = NatInduction (const p)

public export
NatIteration : (p : Type) -> p -> (p -> p) -> Nat -> p
NatIteration p p0 f = NatRecursion p p0 (const f)

infixl 5 +
infixl 6 *

public export
(+) : Nat -> Nat -> Nat
Z + k = k
(S n) + k = S (n + k)

public export
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

