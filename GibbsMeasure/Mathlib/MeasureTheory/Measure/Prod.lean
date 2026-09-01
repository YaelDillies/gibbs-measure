module

public import Mathlib.MeasureTheory.Measure.Prod

public section

open scoped ENNReal
open Filter

namespace MeasureTheory.Measure

section AEEqMul
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}

/-- If `∫⁻ f ∂μ = 1`, then `g` is a.e. equal to `f` times its integral iff
`g x * f y = g y * f x` for `μ.prod μ`-a.e. `(x, y)`. -/
lemma ae_eq_mul_lintegral_iff_ae_mul_comm [SFinite μ]
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∫⁻ x, f x ∂μ = 1) :
    (g =ᵐ[μ] fun x ↦ f x * ∫⁻ y, g y ∂μ) ↔
      ∀ᵐ z ∂μ.prod μ, g z.1 * f z.2 = g z.2 * f z.1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [quasiMeasurePreserving_fst.ae h, quasiMeasurePreserving_snd.ae h] with z h1 h2
    rw [h1, h2]
    ac_rfl
  · filter_upwards [ae_ae_of_ae_prod h] with x hx
    have := lintegral_congr_ae hx
    rw [lintegral_const_mul _ hf, lintegral_mul_const _ hg, hf1, mul_one] at this
    rw [this, mul_comm]

end AEEqMul

variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y]

lemma eq_prod_of_dirac_right (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = ν) (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = ν.prod (Measure.dirac y) := by
-- dynkin's pi system lemma
  sorry

lemma eq_prod_of_dirac_left (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) (marg_Y : Measure.map Prod.snd μ = ν) :
    μ = (Measure.dirac x).prod ν := by
  sorry

end MeasureTheory.Measure
