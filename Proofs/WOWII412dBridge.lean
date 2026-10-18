import Proofs.WOWII412dAssembly
import FormalConjectures.WrittenOnTheWallII.GraphConjecture412d

/-!
# WOWII 412d: certified bridge from the core/critical checkpoint

This file proves that the exact definitions used by the upstream statement
agree with the independently compiled partial development, and derives
corona = criticalUnion for every finite bipartite graph.

The total domination inequality remains a separate, open obligation.
-/

namespace WOWII412dBridge

open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

private theorem independent_iff (I : Finset V) :
    WOWII412dCore.Independent G I ↔ G.IsIndepSet (I : Set V) :=
  WOWII412dCore.independent_iff G I

private theorem difference_eq (I : Finset V) :
    WOWII412dCore.difference G I =
      WrittenOnTheWallII.GraphConjecture412d.difference G I := by
  rfl

private theorem maximum_iff (I : Finset V) :
    WOWII412dCore.Maximum G I ↔
      WrittenOnTheWallII.GraphConjecture412d.IsMaximumIndependent G I := by
  constructor
  · rintro ⟨hi, hm⟩
    exact ⟨(independent_iff G I).mp hi,
      fun J hj => hm J ((independent_iff G J).mpr hj)⟩
  · rintro ⟨hi, hm⟩
    exact ⟨(independent_iff G I).mpr hi,
      fun J hj => hm J ((independent_iff G J).mp hj)⟩

private theorem critical_iff (I : Finset V) :
    WOWII412dCore.Critical G I ↔
      WrittenOnTheWallII.GraphConjecture412d.IsCriticalIndependent G I := by
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨(independent_iff G I).mp hi, ?_⟩
    intro J hj
    simpa only [← difference_eq G J, ← difference_eq G I] using
      hm J ((independent_iff G J).mpr hj)
  · rintro ⟨hi, hm⟩
    refine ⟨(independent_iff G I).mpr hi, ?_⟩
    intro J hj
    simpa only [difference_eq G J, difference_eq G I] using
      hm J ((independent_iff G J).mp hj)

private theorem maximumCritical_iff (I : Finset V) :
    WOWII412dCore.MaximumCritical G I ↔
      WrittenOnTheWallII.GraphConjecture412d.IsMaximumCriticalIndependent G I := by
  constructor
  · rintro ⟨hi, hm⟩
    exact ⟨(critical_iff G I).mp hi,
      fun J hj => hm J ((critical_iff G J).mpr hj)⟩
  · rintro ⟨hi, hm⟩
    exact ⟨(critical_iff G I).mpr hi,
      fun J hj => hm J ((critical_iff G J).mp hj)⟩

private theorem corona_eq :
    WOWII412dCore.corona G =
      WrittenOnTheWallII.GraphConjecture412d.corona G := by
  classical
  ext v
  simp only [WOWII412dCore.corona,
    WrittenOnTheWallII.GraphConjecture412d.corona,
    mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, (maximum_iff G I).mp hI, hv⟩
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, (maximum_iff G I).mpr hI, hv⟩

private theorem criticalUnion_eq :
    WOWII412dCore.criticalUnion G =
      WrittenOnTheWallII.GraphConjecture412d.criticalUnion G := by
  classical
  ext v
  simp only [WOWII412dCore.criticalUnion,
    WrittenOnTheWallII.GraphConjecture412d.criticalUnion,
    mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, (maximumCritical_iff G I).mp hI, hv⟩
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, (maximumCritical_iff G I).mpr hI, hv⟩

/-- The critical union in the actual Formal Conjectures statement equals
the corona, for every finite bipartite graph. This proves the equality
half of the strengthened conjecture without new axioms. -/
theorem criticalUnion_eq_corona (hb : G.IsBipartite) :
    WrittenOnTheWallII.GraphConjecture412d.corona G =
      WrittenOnTheWallII.GraphConjecture412d.criticalUnion G := by
  calc
    WrittenOnTheWallII.GraphConjecture412d.corona G =
        WOWII412dCore.corona G := (corona_eq G).symm
    _ = WOWII412dCore.criticalUnion G :=
      (WOWII412dCore.criticalUnion_eq_corona_of_bipartite G hb).symm
    _ = WrittenOnTheWallII.GraphConjecture412d.criticalUnion G :=
      criticalUnion_eq G

end WOWII412dBridge

#print axioms WOWII412dBridge.criticalUnion_eq_corona
