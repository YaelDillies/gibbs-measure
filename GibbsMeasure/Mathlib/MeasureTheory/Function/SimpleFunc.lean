module

public import Mathlib.MeasureTheory.Function.SimpleFunc

public section

/-!
# TODO

Make `MeasurableSpace α` implicit in `SimpleFunc.induction`
-/

namespace MeasureTheory.SimpleFunc

scoped infixr:25 " →ₛ " => SimpleFunc
scoped notation:25 α:26 " →ₛ[" mα "] " β:25 => @SimpleFunc α mα β

end MeasureTheory.SimpleFunc
