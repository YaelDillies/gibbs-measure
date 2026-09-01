module

public import Mathlib.MeasureTheory.Measure.GiryMonad

public section

open scoped ENNReal
open Filter

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

lemma bind_null {m : Measure α} {f : α → Measure β} {s : Set β}
    (hs : MeasurableSet s) (hf : AEMeasurable f m) :
    m.bind f s = 0 ↔ (fun a ↦ f a s) =ᵐ[m] 0 := by
  rw [bind_apply hs hf]
  exact lintegral_eq_zero_iff' (f := fun a ↦ f a s) <|
    (measurable_coe hs).comp_aemeasurable hf

theorem ae_bind_iff {m : Measure α} {f : α → Measure β} {p : β → Prop}
    (hf : AEMeasurable f m) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ b ∂m.bind f, p b) ↔ ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b :=
  ⟨ae_ae_of_ae_bind hf, fun h ↦ by rwa [ae_iff, bind_null hp.compl hf] at *⟩

end MeasureTheory.Measure
