module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

open ENNReal MeasureTheory Integrable

attribute [fun_prop] MeasureTheory.IntegrableOn

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
  {g : α → ℝ≥0∞}

@[fun_prop]
public lemma integrableOn_toReal (t : Set α) (hm : m ≤ m0) (hgm : AEStronglyMeasurable[m] g μ)
   (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤) :
  IntegrableOn (fun x ↦ (g x).toReal) t μ :=
    integrableOn (s := t) <| integrable_toReal_of_lintegral_ne_top (hgm.mono hm).aemeasurable <|
      by simpa using hg_int_finite Set.univ (by simp) (by simp)
