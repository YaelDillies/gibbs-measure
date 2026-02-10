module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic

public section

namespace MeasureTheory
variable {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}

-- TODO: Replace `measurable_one`
@[to_additive (attr := measurability, fun_prop)]
lemma measurable_one' [One α] : Measurable (1 : β → α) := @measurable_const _ _ _ _ 1

end MeasureTheory
