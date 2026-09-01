/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closure properties of `DependsOn`

Functions depending on a fixed set of coordinates are closed under the pointwise algebraic
operations; those lemmas reduce to `DependsOn.comp` and `DependsOn.comp₂`. Finite sums and
pointwise limits are also covered (`DependsOn.sum`, `DependsOn.of_tendsto`).
-/

public section

variable {ι : Type*} {α : ι → Type*} {β γ δ : Type*} {s : Set ι}
  {f g : (Π i, α i) → β}

/-- Post-composing with an arbitrary function preserves dependence. -/
theorem DependsOn.comp (F : β → γ) (hf : DependsOn f s) : DependsOn (fun x ↦ F (f x)) s :=
  fun _ _ h ↦ congrArg F (hf h)

/-- Combining two functions depending on `s` by an arbitrary binary operation preserves
dependence. This is the source of all the pointwise algebraic closure properties below. -/
theorem DependsOn.comp₂ (F : β → γ → δ) {g : (Π i, α i) → γ}
    (hf : DependsOn f s) (hg : DependsOn g s) : DependsOn (fun x ↦ F (f x) (g x)) s :=
  fun _ _ h ↦ by simp only [hf h, hg h]

section Algebra

@[to_additive]
theorem DependsOn.mul [Mul β] (hf : DependsOn f s) (hg : DependsOn g s) :
    DependsOn (fun x ↦ f x * g x) s := DependsOn.comp₂ (· * ·) hf hg

@[to_additive]
theorem DependsOn.inv [Inv β] (hf : DependsOn f s) : DependsOn (fun x ↦ (f x)⁻¹) s :=
  DependsOn.comp _ hf

@[to_additive]
theorem DependsOn.div [Div β] (hf : DependsOn f s) (hg : DependsOn g s) :
    DependsOn (fun x ↦ f x / g x) s := DependsOn.comp₂ (· / ·) hf hg

@[to_additive]
theorem DependsOn.pow [Monoid β] (hf : DependsOn f s) (n : ℕ) :
    DependsOn (fun x ↦ f x ^ n) s := DependsOn.comp (· ^ n) hf

theorem DependsOn.smul {M : Type*} [SMul M β] (c : M) (hf : DependsOn f s) :
    DependsOn (fun x ↦ c • f x) s := DependsOn.comp (c • ·) hf

theorem DependsOn.sup [Max β] (hf : DependsOn f s) (hg : DependsOn g s) :
    DependsOn (fun x ↦ f x ⊔ g x) s := DependsOn.comp₂ (· ⊔ ·) hf hg

theorem DependsOn.inf [Min β] (hf : DependsOn f s) (hg : DependsOn g s) :
    DependsOn (fun x ↦ f x ⊓ g x) s := DependsOn.comp₂ (· ⊓ ·) hf hg

end Algebra

/-- A finite sum of functions depending on `s` depends on `s`. -/
theorem DependsOn.sum {κ : Type*} [AddCommMonoid β] {t : Finset κ} {F : κ → (Π i, α i) → β}
    (hF : ∀ k ∈ t, DependsOn (F k) s) : DependsOn (fun x ↦ ∑ k ∈ t, F k x) s := by
  classical
  intro x y h
  exact Finset.sum_congr rfl fun k hk ↦ hF k hk h

/-- A pointwise limit of functions depending on `s` depends on `s`. -/
theorem DependsOn.of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot] [TopologicalSpace β] [T2Space β]
    {F : κ → (Π i, α i) → β} {f : (Π i, α i) → β}
    (hF : ∀ k, DependsOn (F k) s) (hlim : ∀ x, Filter.Tendsto (F · x) l (nhds (f x))) :
    DependsOn f s := by
  intro x y hxy
  exact tendsto_nhds_unique (by simpa only [hF _ hxy] using hlim x) (hlim y)

