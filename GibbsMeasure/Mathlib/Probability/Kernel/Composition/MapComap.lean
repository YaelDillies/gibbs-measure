module

public import Mathlib.Probability.Kernel.Composition.MapComap

public section

namespace ProbabilityTheory.Kernel
variable {α β : Type*} {mα mα' : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Unfolds the coercion `mα ≤ mα'` → `Measurable id`. -/
lemma comap_id_le (κ : @Kernel α β mα mβ) (h : mα ≤ mα') :
    κ.comap id h = κ.comap id (measurable_id'' h) :=
  DFunLike.ext _ _ fun _ ↦ rfl

end ProbabilityTheory.Kernel
