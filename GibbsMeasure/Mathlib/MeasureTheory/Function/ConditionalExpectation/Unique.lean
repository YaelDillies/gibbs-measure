module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
public import Mathlib.MeasureTheory.Function.SimpleFunc

public section

open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α}

/-! **Uniqueness of the Lebesgue conditional expectation** -/
theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hfg_eq : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  sorry

end MeasureTheory
