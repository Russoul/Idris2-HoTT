module Unit

import Basic

%default total

public export
data Unit : Type where
  MkUnit : Unit

public export
UnitInduction : (p : Unit -> Type) -> p () -> (x : Unit) -> p x
UnitInduction _ prop () = prop

public export
UnitRecursion : (p : Type) -> p -> Unit -> p
UnitRecursion _ p () = p

public export
UnitTerminal : (p : Type) -> p -> Unit
UnitTerminal _ = const ()
