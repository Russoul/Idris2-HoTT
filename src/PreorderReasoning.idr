module PreorderReasoning

import Basic
import Path

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
  Chain (p |=> (_ ... f)) = f `compose` Chain p

