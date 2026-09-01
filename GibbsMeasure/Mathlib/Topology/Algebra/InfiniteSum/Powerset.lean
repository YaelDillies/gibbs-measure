/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summation along the powerset net

For a family indexed by `Finset ι`, `SummationFilter.powerset ι` sums along the net of partial
sums over `{A | A ⊆ s}`, as `s : Finset ι` ranges over `atTop`.

This is coarser than unconditional summation, so `Summable f` implies
`Summable f (SummationFilter.powerset ι)` with the same sum.
-/

@[expose] public section

open Filter

namespace SummationFilter

variable (ι : Type*)

/-- Summation along the net of partial sums over the subsets of a finite set, as that set
ranges over `atTop`. -/
def powerset : SummationFilter (Finset ι) := ⟨Filter.map Finset.powerset atTop⟩

variable {ι}

lemma powerset_filter : (powerset ι).filter = Filter.map Finset.powerset atTop := rfl

instance : (powerset ι).LeAtTop := ⟨Filter.tendsto_finset_powerset_atTop_atTop⟩

instance : (powerset ι).NeBot := ⟨Filter.map_neBot⟩

instance [Countable ι] : (powerset ι).filter.IsCountablyGenerated := by
  rw [powerset_filter]
  infer_instance

lemma tendsto_powerset_filter {α : Type*} [TopologicalSpace α] {f : Finset (Finset ι) → α} {a : α}
    (h : Tendsto (fun s : Finset ι ↦ f s.powerset) atTop (nhds a)) :
    Tendsto f (powerset ι).filter (nhds a) :=
  tendsto_map' h

lemma hasSum_powerset_iff {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f : Finset ι → α} {a : α} :
    HasSum f a (powerset ι) ↔
      Tendsto (fun s : Finset ι ↦ ∑ i ∈ s.powerset, f i) atTop (nhds a) := by
  rw [HasSum, powerset_filter, tendsto_map'_iff, Function.comp_def]

end SummationFilter

namespace HasSum

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α} {a : α}

/-- Unconditional summability implies summability along `SummationFilter.powerset`, with the same
sum. -/
lemma powerset (h : HasSum f a) : HasSum f a (SummationFilter.powerset ι) :=
  h.mono_left (SummationFilter.le_atTop (L := SummationFilter.powerset ι))

end HasSum

namespace Summable

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α}

lemma powerset (h : Summable f) : Summable f (SummationFilter.powerset ι) :=
  h.mono_filter (SummationFilter.le_atTop (L := SummationFilter.powerset ι))

end Summable
