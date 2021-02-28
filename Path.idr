module Path

import Basic
import Unit
import Void

||| Type of identities or paths between two points in space.
public export
data Id : (0 a : Type) -> a -> a -> Type where
  Refl : (x : a) -> Id a x x

infix 4 ==

public export
(==) : a -> a -> Type
x == y = Id _ x y

||| Induction principle for paths
public export
J : (p : (x, y : a) -> (x == y) -> Type)
 -> ((x : a) -> p x x (Refl x))
 -> (x, y : a) -> (i : x == y) -> p x y i
J p f x x (Refl x) = f x

-- Another one
public export
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

public export
transport : (p : a -> Type) -> {x, y : _} -> x == y -> p x -> p y
transport p i = J (\x, y, _ => p x -> p y) (\_ => id) _ _ i

public export
IdFun : {a, b: Type} -> a == b -> a -> b
IdFun = transport id

public export
transportConst : (a, b : Type)
              -> (x, y : a)
              -> (x' : b)
              -> (path : Id a x y)
              -> transport (\_ => b) path x' == x'
transportConst a b x x x' (Refl x) = Refl x'

namespace Id
  public export
  (.) : {x, y, z : a} -> x == y -> y == z -> x == z
  p . q = transport (x ==) q p

||| p <=> p⁻¹
public export
sym : {x, y : a} -> (p : x == y) -> y == x
sym p = transport (== x) p (Refl x)

||| Congurence or f(p) in the HoTT book
||| p => f(p)
public export
ap : {x, y : a} -> (f : a -> b) -> (p : x == y) -> f x == f y
ap f p = transport (\that => f x == f that) p (Refl (f x))

|||Dependent map
public export
apd : (p : a -> Type)
   -> (f : (x : a) -> p x)
   -> (x, y : a)
   -> (path : x == y)
   -> transport p path (f x) == f y
apd p f x x (Refl x) = Refl (f x)


