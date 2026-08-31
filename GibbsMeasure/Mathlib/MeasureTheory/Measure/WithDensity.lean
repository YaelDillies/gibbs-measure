module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

public section

open scoped ENNReal

namespace MeasureTheory.Measure
variable {α : Type*} {mα : MeasurableSpace α}

@[fun_prop]
lemma measurable_withDensity {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α ↦ μ.withDensity f :=
  measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [withDensity_apply _ hs]
    exact measurable_setLIntegral hf hs

end MeasureTheory.Measure
