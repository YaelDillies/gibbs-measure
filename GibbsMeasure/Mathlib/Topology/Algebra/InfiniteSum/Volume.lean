/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summation over finite subsets, ordered by inclusion

For a family indexed by `Finset ι`, `SummationFilter.volume ι` sums along the net of partial sums
over `{A | A ⊆ Δ}`, as `Δ : Finset ι` ranges over `atTop`.

This is coarser than unconditional summation, so `Summable f` implies
`Summable f (SummationFilter.volume ι)` with the same sum.
-/

@[expose] public section

open Filter

namespace SummationFilter

variable (ι : Type*)

/-- Summation along the net of partial sums over the subsets of a finite volume. -/
def volume : SummationFilter (Finset ι) := ⟨Filter.map Finset.powerset atTop⟩

variable {ι}

lemma volume_filter : (volume ι).filter = Filter.map Finset.powerset atTop := rfl

instance : (volume ι).LeAtTop := ⟨Filter.tendsto_finset_powerset_atTop_atTop⟩

instance : (volume ι).NeBot := ⟨Filter.map_neBot⟩

instance [Countable ι] : (volume ι).filter.IsCountablyGenerated := by
  rw [volume_filter]; infer_instance

lemma tendsto_volume_filter {α : Type*} [TopologicalSpace α] {f : Finset (Finset ι) → α} {a : α}
    (h : Tendsto (fun Δ : Finset ι ↦ f Δ.powerset) atTop (nhds a)) :
    Tendsto f (volume ι).filter (nhds a) := h

end SummationFilter

namespace HasSum

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α} {a : α}

/-- Unconditional summability implies summability along `SummationFilter.volume`, with the same
sum. -/
lemma volume (h : HasSum f a) : HasSum f a (SummationFilter.volume ι) :=
  h.mono_left (SummationFilter.le_atTop (L := SummationFilter.volume ι))

end HasSum

namespace Summable

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α}

lemma volume (h : Summable f) : Summable f (SummationFilter.volume ι) :=
  h.mono_filter (SummationFilter.le_atTop (L := SummationFilter.volume ι))

end Summable
