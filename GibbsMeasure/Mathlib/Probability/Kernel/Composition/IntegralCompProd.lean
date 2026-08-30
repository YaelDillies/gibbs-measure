module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_comp {f : β → E} (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ b, f b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ := by
  rw [comp_eq_comp_const_apply] at hf ⊢
  simpa [Kernel.const_apply] using Kernel.integral_comp hf

end MeasureTheory.Measure
