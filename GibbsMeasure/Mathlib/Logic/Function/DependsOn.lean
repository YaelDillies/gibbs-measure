/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closure properties of `DependsOn`
-/

@[expose] public section

variable {ι : Type*} {α : ι → Type*} {β γ δ : Type*} {s : Set ι}
  {f g : (Π i, α i) → β}

theorem DependsOn.comp (F : β → γ) (hf : DependsOn f s) : DependsOn (fun x ↦ F (f x)) s :=
  fun _ _ h ↦ congrArg F (hf h)

theorem DependsOn.comp₂ (F : β → γ → δ) {g : (Π i, α i) → γ}
    (hf : DependsOn f s) (hg : DependsOn g s) : DependsOn (fun x ↦ F (f x) (g x)) s :=
  fun _ _ h ↦ by simp only [hf h, hg h]

lemma dependsOn_of_const (b : β) : DependsOn (fun _ : Π i, α i ↦ b) s := fun _ _ _ ↦ rfl

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

theorem DependsOn.sum {κ : Type*} [AddCommMonoid β] {t : Finset κ} {F : κ → (Π i, α i) → β}
    (hF : ∀ k ∈ t, DependsOn (F k) s) : DependsOn (fun x ↦ ∑ k ∈ t, F k x) s :=
  fun _ _ h ↦ Finset.sum_congr rfl fun k hk ↦ hF k hk h

theorem DependsOn.of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot] [TopologicalSpace β] [T2Space β]
    {F : κ → (Π i, α i) → β} {f : (Π i, α i) → β}
    (hF : ∀ k, DependsOn (F k) s) (hlim : ∀ x, Filter.Tendsto (F · x) l (nhds (f x))) :
    DependsOn f s :=
  fun x y hxy ↦ tendsto_nhds_unique ((hlim x).congr fun k ↦ hF k hxy) (hlim y)
