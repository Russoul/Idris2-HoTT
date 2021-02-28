module Void

import Basic

%default total

public export
data Void : Type where

public export
VoidInduction : (0 p : Void -> Type) -> (0 x : Void) -> p x
VoidInduction _ x impossible

public export
VoidRecursion : (0 p : Type) -> (0 x : Void) -> p
VoidRecursion p = VoidInduction (const p)

public export
VoidInitial : (0 p : Type) -> (0 x : Void) -> p
VoidInitial = VoidRecursion

public export
IsEmpty : Type -> Type
IsEmpty a = a -> Void

public export
Neg : Type -> Type
Neg = IsEmpty

