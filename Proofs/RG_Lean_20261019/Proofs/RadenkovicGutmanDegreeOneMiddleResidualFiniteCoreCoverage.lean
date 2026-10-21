/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeyLookup
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def armsCovered (n i : ℕ) : Bool :=
  decide (∀ p q : Fin 5, (n,p.val,q.val) ∈ domains →
    keyArray[lookup n i p.val q.val]?=some (⟨n,i,p.val,q.val⟩ : Key))
def coreCovered (n i : ℕ) : Bool :=
  if rootDegree (representative n i)=1 then armsCovered n i else true
theorem core_sound (n i : ℕ) (hc : coreCovered n i=true) (p q : Fin 5)
    (he : eligible n i p.val q.val=true) :
    keyArray[lookup n i p.val q.val]?=some (⟨n,i,p.val,q.val⟩ : Key) := by
  have hh : rootDegree (representative n i)=1 ∧ (n,p.val,q.val) ∈ domains := by
    simpa only [eligible,Bool.and_eq_true,decide_eq_true_eq] using he
  have ha : armsCovered n i=true := by simpa only [coreCovered,if_pos hh.1] using hc
  exact of_decide_eq_true ha p q hh.2
def coveredRange (n start count : ℕ) : Bool :=
  decide (∀ i : Fin count, coreCovered n (start+i.val)=true)
theorem range_sound (n start count : ℕ) (hc : coveredRange n start count=true)
    (i : ℕ) (p q : Fin 5) (hlo : start ≤ i) (hhi : i < start+count)
    (he : eligible n i p.val q.val=true) : (⟨n,i,p.val,q.val⟩ : Key) ∈ keys := by
  have hh := of_decide_eq_true hc (⟨i-start,by omega⟩ : Fin count)
  have hi : start+(i-start)=i := by omega
  dsimp only [Fin.val_mk] at hh
  rw [hi] at hh
  rw [← keyArray_toList]
  exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? (core_sound n i hh p q he))
#print axioms core_sound
#print axioms range_sound
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys.CoreCoverage
