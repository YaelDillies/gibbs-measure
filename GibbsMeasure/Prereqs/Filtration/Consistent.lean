module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Process.Filtration

/-!
# TODO

Reopen https://github.com/leanprover-community/mathlib4/pull/17859 once we have more API depending
on this definition.
-/

@[expose] public section

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

namespace MeasureTheory.Filtration
variable {X P S E : Type*} {mX : MeasurableSpace X} {mE : MeasurableSpace E} [PartialOrder P]

/-- A family of kernels `γ` on `X` indexed by a partial order `P` is consistent under conditioning
if `γ p₂ ∘ₖ γ p₁ = γ p₁` whenever `p₁ ≤ p₂`. -/
def IsConsistentKernel (mXs : Filtration P mX) (γ : ∀ p, Kernel[mXs p] X X) : Prop :=
  ∀ ⦃p₁ p₂⦄, p₁ ≤ p₂ → (γ p₂).comap id (mXs.le p₂) ∘ₖ γ p₁ = γ p₁

end MeasureTheory.Filtration
