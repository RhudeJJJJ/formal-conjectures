/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteBounds
import Proofs.RadenkovicGutmanDegreeTwoThreeClassAssembly
import Proofs.RadenkovicGutmanRootedCatalogueComplete
import Proofs.RadenkovicGutmanCoreTreeTransfer

namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteTransfer
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open RootedTreeEnumeration SmallGeFourKeys FiniteTreeTransfer
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def Coverage : Prop :=
  ∀ (n : ℕ), n ≤ 10 → ∀ (i : Fin (RootedCatalogueData.catalogue n).length)
    (p q : Fin 13), DegreeTwoThreeFiniteKeys.eligible n i.val p.val q.val=true →
      (⟨n,i.val,p.val,q.val⟩ : Key) ∈ DegreeTwoThreeFiniteKeys.keys

def Certificates : Prop :=
  ∀ n i p q : ℕ, (⟨n,i,p,q⟩ : Key) ∈ DegreeTwoThreeFiniteKeys.keys →
    Certified (graph (representative n i)) (root n) p q

/-- Exact coverage and certified catalogue comparisons imply the original
finite family on arbitrary actual trees, below each pair's own class cutoff. -/
theorem finite_cases (hcoverage : Coverage) (hcertificates : Certificates) :
    DegreeTwoThreeClassAssembly.FiniteCases := by
  intro m C u p q hT hd hN
  have hCore := core_tree C u p q hT
  have hm : 0 < m := by have := u.isLt; omega
  have hdegree : C.degree u < m := by
    simpa only [Fintype.card_fin] using C.degree_lt_card_verts u
  simp only [order,Fintype.card_sum,Fintype.card_fin] at hN
  have hsmall : m+p+q+2 < DegreeTwoThreeThresholds.threshold (C.degree u) p q := by omega
  obtain ⟨hcore,hp,hq⟩ := DegreeTwoThreeThresholds.finite_parameters
    m (C.degree u) p q hd hdegree hsmall
  let n := m-1
  have hc : m=n+1 := by dsimp [n]; omega
  have hn : n ≤ 10 := by omega
  obtain ⟨i,e,he⟩ := RootedCatalogueData.all_actual_trees C u hCore n hn
    (by simpa only [Fintype.card_fin] using hc)
  have hdeg : rootDegree (representative n i.val)=C.degree u := by
    rw [representative_get,rootDegree_eq_degree,← he,e.degree_eq]
  have helig : DegreeTwoThreeFiniteKeys.eligible n i.val p q=true := by
    simp only [DegreeTwoThreeFiniteKeys.eligible,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rw [hdeg]
      exact hd
    · rw [hdeg]
      omega
  have hk := hcoverage n hn i ⟨p,hp⟩ ⟨q,hq⟩ helig
  have hcert := hcertificates n i.val p q hk
  rw [representative_get n i] at hcert
  have hactual : Certified C u p q :=
    certified_transport e u p q (by simpa only [he] using hcert)
  exact positive_of_certified C u p q hT (by omega) hactual

#print axioms finite_cases
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteTransfer
