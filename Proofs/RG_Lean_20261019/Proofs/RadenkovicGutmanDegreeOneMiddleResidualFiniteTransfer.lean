/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorAssembly
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData
import Proofs.RadenkovicGutmanRootedCatalogueComplete
import Proofs.RadenkovicGutmanCoreTreeTransfer

namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteTransfer
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open RootedTreeEnumeration SmallGeFourKeys FiniteTreeTransfer
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

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

def Coverage : Prop :=
  ∀ (n : ℕ), n ≤ 10 → ∀ (i : Fin (RootedCatalogueData.catalogue n).length)
    (p q : Fin 5), DegreeOneMiddleResidualFiniteKeys.eligible n i.val p.val q.val=true →
      (⟨n,i.val,p.val,q.val⟩ : Key) ∈ DegreeOneMiddleResidualFiniteKeys.keys

def Certificates : Prop :=
  ∀ n i p q : ℕ, (⟨n,i,p,q⟩ : Key) ∈ DegreeOneMiddleResidualFiniteKeys.keys →
    Certified (graph (representative n i)) (root n) p q

/-- All rooted catalogue cores, both unequal arm orders and the original mean
threshold are transported to arbitrary actual residual trees. -/
theorem residual_cases (hcoverage : Coverage) (hcertificates : Certificates) :
    DegreeOneMiddleAnchors.ResidualCases := by
  intro m C u p q hT hd hr
  have hm : 0 < m := by have := u.isLt; omega
  have horder : order C p q=m+p+q+2 := by
    simp only [order,Fintype.card_sum,Fintype.card_fin]
    omega
  rw [horder] at hr
  obtain ⟨hcore,hp,hq,hdom⟩ := residual_parameters m p q hm hr
  have hCore := core_tree C u p q hT
  let n := m-1
  have hc : m=n+1 := by dsimp [n]; omega
  have hn : n ≤ 10 := by omega
  obtain ⟨i,e,he⟩ := RootedCatalogueData.all_actual_trees C u hCore n hn
    (by simpa only [Fintype.card_fin] using hc)
  have hdeg : rootDegree (representative n i.val)=C.degree u := by
    rw [representative_get,rootDegree_eq_degree,← he,e.degree_eq]
  have helig : DegreeOneMiddleResidualFiniteKeys.eligible n i.val p q=true := by
    simp only [DegreeOneMiddleResidualFiniteKeys.eligible,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hdeg.trans hd,hdom⟩
  have hk := hcoverage n hn i ⟨p,hp⟩ ⟨q,hq⟩ helig
  have hcert := hcertificates n i.val p q hk
  rw [representative_get n i] at hcert
  have hactual : Certified C u p q :=
    certified_transport e u p q (by simpa only [he] using hcert)
  exact positive_of_certified C u p q hT (by omega) hactual

#print axioms residual_parameters
#print axioms residual_cases
end
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteTransfer
