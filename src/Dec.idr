module Dec

import Basic
import Unit
import Void
import Coproduct

import Path
import General

public export
Dec : Type -> Type
Dec a = a + Neg a

public export
DecEq : Type -> Type
DecEq a = (x, y : a) -> Dec (x == y)


