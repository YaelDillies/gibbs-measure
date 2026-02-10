module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.ENNReal.Basic

public section

namespace ENNReal
variable {α : Type*}

@[simp] lemma ofReal_indicator_one (s : Set α) (a : α) :
    ENNReal.ofReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

@[simp] lemma tOReal_indicator_one (s : Set α) (a : α) :
    ENNReal.toReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

end ENNReal
