module

public import Mathlib.MeasureTheory.Measure.GiryMonad

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

theorem measurable_of_measurable_coe' (t : Set (Set α)) (μ : β → Measure[.generateFrom t] α)
    [∀ b, IsProbabilityMeasure (μ b)] (h : ∀ s ∈ t, Measurable fun b => μ b s) : Measurable μ := by
  refine @measurable_of_measurable_coe _ _ (_) _ _ fun {s} hs ↦
    MeasurableSpace.generateFrom_induction (p := fun s _ ↦ Measurable fun b ↦ μ b s) t
      (fun s hs _ ↦ h s hs) (by simp) ?_ ?_ _ hs
  · rintro s hs_meas hs
    simp_rw [prob_compl_eq_one_sub hs_meas]
    exact hs.const_sub _
  · rintro g hg_meas hg
    rw [← iUnion_disjointed]
    simp_rw [measure_iUnion (disjoint_disjointed _) (.disjointed hg_meas)]
    refine .tsum fun i ↦ ?_
    sorry

variable {mα : MeasurableSpace α} {s : Set α}

lemma measurable_restrict (hs : MeasurableSet s) : Measurable fun μ : Measure α ↦ μ.restrict s :=
  measurable_of_measurable_coe _ fun t ht ↦ by
    simp_rw [restrict_apply ht]; exact measurable_coe (ht.inter hs)

lemma measurable_setLIntegral {f : α → ℝ≥0∞} (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable fun μ : Measure α ↦ ∫⁻ x in s, f x ∂μ :=
  (measurable_lintegral hf).comp (measurable_restrict hs)

/-- Converse to `ae_ae_of_ae_bind` for a measurable predicate. -/
lemma ae_bind_iff {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {f : α → Measure β} {p : β → Prop}
    (hf : AEMeasurable f μ) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂μ.bind f, p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ x ∂f a, p x := by
  refine ⟨ae_ae_of_ae_bind hf, fun h ↦ ?_⟩
  have hpc : MeasurableSet {x | ¬p x} := (compl_ofPred p).symm ▸ hp.compl
  rw [ae_iff, bind_apply hpc hf]
  rw [lintegral_eq_zero_iff' (f := fun a ↦ f a {x | ¬p x}) <|
    (measurable_coe hpc).comp_aemeasurable hf]
  filter_upwards [h] with a ha
  simpa [ae_iff] using ha

end MeasureTheory.Measure
