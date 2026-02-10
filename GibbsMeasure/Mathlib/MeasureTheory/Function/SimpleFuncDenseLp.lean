module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.IntegrableOn

public section

open ENNReal Function

namespace MeasureTheory
variable {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E] {μ : Measure α}

-- TODO: Replace in mathlib
@[elab_as_elim]
lemma Integrable.induction' (P : ∀ f : α → E, Integrable f μ → Prop)
    (indicator : ∀ c s (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      P (s.indicator fun _ ↦ c) ((integrable_indicator_iff hs).2 integrableOn_const))
    (add : ∀ (f g : α → E) (hf : Integrable f μ) (hg : Integrable g μ),
        Disjoint (support f) (support g) → P f hf → P g hg → P (f + g) (hf.add hg))
    (isClosed : IsClosed {f : α →₁[μ] E | P f (L1.integrable_coeFn f)})
    (ae_congr : ∀ (f g) (hf : Integrable f μ) (hfg : f =ᵐ[μ] g), P f hf → P g (hf.congr hfg)) :
    ∀ (f : α → E) (hf : Integrable f μ), P f hf := by
  sorry

namespace SimpleFunc
variable {mα₀ : MeasurableSpace α}

lemma integrable_of_isFiniteMeasure' (hα : mα₀ ≤ mα) [IsFiniteMeasure μ] (f : α →ₛ[mα₀] E) :
    Integrable f μ := sorry

end MeasureTheory.SimpleFunc
