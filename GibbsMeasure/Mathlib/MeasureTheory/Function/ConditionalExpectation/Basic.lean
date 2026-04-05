module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

open TopologicalSpace MeasureTheory Lp Filter Measure Integrable
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory
variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

--TODO : Generalise to SigmaFinite (μ.trim hm) ?
variable [IsFiniteMeasure μ]

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
    {g : α → ℝ≥0∞} {s : Set α} (hs₀ : MeasurableSet[m] s) (hgm : AEStronglyMeasurable[m] g μ)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t)) :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  have : AEStronglyMeasurable[m0] g μ := hgm.mono hm
  refine ae_eq_condExp_of_forall_setIntegral_eq (f := s.indicator fun _ ↦ (1 : ℝ))
    hm (by fun_prop (disch := measurability))
    (fun t ht hμt ↦ integrableOn_toReal _ hm hgm fun t ht hμt ↦ by rw [hg_eq _ ht hμt]; finiteness)
    (fun t ht hμt ↦ ?_) ?_
  · have hg_ae : ∀ᵐ x ∂μ.restrict t, g x < ∞ := ae_lt_top' (hgm.mono hm).aemeasurable.restrict
      (by simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt)
    calc
      ∫ x in t, (g x).toReal ∂μ = ∫ x in t ∩ s, (1 : ℝ) ∂μ := by
        simp [integral_toReal (hgm.mono hm).aemeasurable.restrict hg_ae, hg_eq t ht hμt,
          measureReal_def, Set.inter_comm]
      _ = ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ := by
        rw [← setIntegral_indicator (hm s hs₀)]
  · exact hgm.stronglyMeasurable_mk.measurable.ennreal_toReal.aestronglyMeasurable.congr
      (hgm.ae_eq_mk.fun_comp ENNReal.toReal).symm

-- /-- **Uniqueness of the conditional expectation**
-- If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
-- as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
-- theorem toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq (hm : m ≤ m0)
--     [SigmaFinite (μ.trim hm)] {f g : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
--     (hf : ∫⁻ a, f a ∂μ ≠ ⊤)
--     (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ a in s, g a ∂μ ≠ ⊤)
--     (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, f x ∂μ)
--     (hgm : AEStronglyMeasurable[m] g μ) :
--     (fun a ↦ (g a).toReal) =ᵐ[μ] μ[fun a ↦ (f a).toReal|m] := by
--   refine ae_eq_condExp_of_forall_setIntegral_eq hm
--     (integrable_toReal_of_lintegral_ne_top hf_meas hf)
--     (fun s hs hs_fin ↦ integrable_toReal_of_lintegral_ne_top _ _) _ _

lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α} :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1| m] ↔
      ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := sorry

end MeasureTheory
