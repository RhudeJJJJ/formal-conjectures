/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeyLookup
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
open SmallGeFourKeys DegreeTwoThreeThresholds
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def armsCovered (d n i : ℕ) : Bool :=
  decide (∀ p q : Fin 13, n+p.val+q.val+3<threshold d p.val q.val →
    keyArray[lookup n i p.val q.val]?=some (⟨n,i,p.val,q.val⟩ : Key))

/-- Evaluate the actual root degree before enumerating the arm parameters. -/
def coreCovered (n i : ℕ) : Bool :=
  if rootDegree (representative n i)=2 then armsCovered 2 n i
  else if rootDegree (representative n i)=3 then armsCovered 3 n i
  else true

theorem core_sound (n i : ℕ) (hc : coreCovered n i=true) (p q : Fin 13)
    (he : eligible n i p.val q.val=true) :
    keyArray[lookup n i p.val q.val]?=some (⟨n,i,p.val,q.val⟩ : Key) := by
  have he' : (rootDegree (representative n i)=2 ∨ rootDegree (representative n i)=3) ∧
      n+p.val+q.val+3<threshold (rootDegree (representative n i)) p.val q.val := by
    simpa only [eligible,Bool.and_eq_true,decide_eq_true_eq] using he
  rcases he'.1 with h2 | h3
  · have ha : armsCovered 2 n i=true := by
      simpa only [coreCovered,if_pos h2] using hc
    exact of_decide_eq_true ha p q (by simpa only [h2] using he'.2)
  · have hnot2 : rootDegree (representative n i)≠2 := by omega
    have ha : armsCovered 3 n i=true := by
      simpa only [coreCovered,if_neg hnot2,if_pos h3] using hc
    exact of_decide_eq_true ha p q (by simpa only [h3] using he'.2)

def coveredRange (n start count : ℕ) : Bool :=
  decide (∀ i : Fin count, coreCovered n (start+i.val)=true)

theorem range_sound (n start count : ℕ) (hc : coveredRange n start count=true)
    (i : ℕ) (p q : Fin 13) (hlo : start ≤ i) (hhi : i < start + count)
    (he : eligible n i p.val q.val=true) : (⟨n,i,p.val,q.val⟩ : Key) ∈ keys := by
  have hh := of_decide_eq_true hc (⟨i-start,by omega⟩ : Fin count)
  have hi : start+(i-start)=i := by omega
  dsimp only [Fin.val_mk] at hh
  rw [hi] at hh
  rw [← keyArray_toList]
  exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? (core_sound n i hh p q he))

#print axioms core_sound
#print axioms range_sound
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys.CoreCoverage
