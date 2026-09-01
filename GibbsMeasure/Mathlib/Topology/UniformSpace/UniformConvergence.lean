/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Reindexing uniform convergence
-/

@[expose] public section

open Filter

variable {ι κ α β : Type*} [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι}

theorem TendstoUniformlyOn.comp_tendsto {s : Set α} {q : Filter κ} {g : κ → ι}
    (h : TendstoUniformlyOn F f p s) (hg : Tendsto g q p) :
    TendstoUniformlyOn (fun k ↦ F (g k)) f q s :=
  fun u hu ↦ hg.eventually (h u hu)

theorem TendstoUniformly.comp_tendsto {q : Filter κ} {g : κ → ι}
    (h : TendstoUniformly F f p) (hg : Tendsto g q p) :
    TendstoUniformly (fun k ↦ F (g k)) f q :=
  fun u hu ↦ hg.eventually (h u hu)

theorem tendstoUniformly_of_eventually_eq (h : ∀ᶠ n in p, F n = f) :
    TendstoUniformly F f p :=
  fun _u hu ↦ h.mono fun _ hn x ↦ mem_uniformity_of_eq hu (congrFun hn x).symm
