/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverageComplete

/-! The original physical residual parameters are equivalent to the ordered
finite domains. This module deliberately does not import the unfinished
actual-tree catalogue transfer or assume any spectral certificates. -/
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteParameters
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem residual_parameters (m p q : ℕ) (hm : 0 < m)
    (hr : (m+p+q+2,min p q,max p q) ∈ DegreeOneMiddleAnchors.residual) :
    m ≤ 11 ∧ p < 5 ∧ q < 5 ∧ (m-1,p,q) ∈ DegreeOneMiddleResidualFiniteKeys.domains := by
  simp only [DegreeOneMiddleAnchors.residual,List.mem_cons,List.not_mem_nil,
    Prod.mk.injEq,or_false] at hr
  have split (N a b : ℕ) (h : m+p+q+2=N ∧ min p q=a ∧ max p q=b) :
      m=N-a-b-2 ∧ ((p=a ∧ q=b) ∨ (p=b ∧ q=a)) := by omega
  rcases hr with h | h | h | h | h | h | h | h
  all_goals
    obtain ⟨he,hpq⟩ := split _ _ _ h
    rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      subst m
      norm_num [DegreeOneMiddleResidualFiniteKeys.domains]

/-- No residual parameter is lost, and no additional ordered domain is admitted. -/
theorem residual_iff_domain (m p q : ℕ) (hm : 0 < m) :
    (m+p+q+2,min p q,max p q) ∈ DegreeOneMiddleAnchors.residual ↔
      (m-1,p,q) ∈ DegreeOneMiddleResidualFiniteKeys.domains := by
  constructor
  · intro hr
    exact (residual_parameters m p q hm hr).2.2.2
  · intro hd
    simp only [DegreeOneMiddleResidualFiniteKeys.domains,List.mem_cons,
      List.not_mem_nil,Prod.mk.injEq,or_false] at hd
    simp only [DegreeOneMiddleAnchors.residual,List.mem_cons,List.not_mem_nil,
      Prod.mk.injEq,or_false]
    omega

/-- The physical order of every unpaid finite case is between 14 and 17. -/
theorem residual_physical_bounds (m p q : ℕ)
    (hr : (m+p+q+2,min p q,max p q) ∈ DegreeOneMiddleAnchors.residual) :
    14 ≤ m+p+q+2 ∧ m+p+q+2 ≤ 17 ∧ 4 ≤ m ∧ m ≤ 11 ∧
      (p=2 ∨ p=4) ∧ (q=2 ∨ q=4) := by
  simp only [DegreeOneMiddleAnchors.residual,List.mem_cons,List.not_mem_nil,
    Prod.mk.injEq,or_false] at hr
  omega

/-- Join the physical residual classification to the kernel-checked parameter
coverage. Both orientations of unequal arms use the original key list. -/
theorem residual_key_mem (m p q : ℕ) (hm : 0 < m)
    (hr : (m+p+q+2,min p q,max p q) ∈ DegreeOneMiddleAnchors.residual)
    (i : Fin (RootedCatalogueData.catalogue (m-1)).length)
    (hd : rootDegree (representative (m-1) i.val)=1) :
    (⟨m-1,i.val,p,q⟩ : Key) ∈ DegreeOneMiddleResidualFiniteKeys.keys := by
  obtain ⟨hm11,hp,hq,hdom⟩ := residual_parameters m p q hm hr
  have helig : DegreeOneMiddleResidualFiniteKeys.eligible (m-1) i.val p q=true := by
    simp only [DegreeOneMiddleResidualFiniteKeys.eligible,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hd,hdom⟩
  exact DegreeOneMiddleResidualFiniteKeys.parameter_coverage (m-1) (by omega)
    i ⟨p,hp⟩ ⟨q,hq⟩ helig

#print axioms residual_parameters
#print axioms residual_iff_domain
#print axioms residual_physical_bounds
#print axioms residual_key_mem
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteParameters
