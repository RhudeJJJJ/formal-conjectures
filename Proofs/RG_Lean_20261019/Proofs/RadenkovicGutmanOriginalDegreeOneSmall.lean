/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallCoverageComplete
import Proofs.RadenkovicGutmanDegreeOneSmallCertificatesComplete
import Proofs.RadenkovicGutmanRootedCatalogueComplete
import Proofs.RadenkovicGutmanCoreTreeTransfer
import Proofs.RadenkovicGutmanOriginalAssembly
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeOneSmall
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open RootedTreeEnumeration SmallGeFourKeys FiniteTreeTransfer
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Candidate complete original degree-one small-order family. -/
theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=1) (hN : order C p q≤13) :
    0<meanIntegral C u p q := by
  have hCore := core_tree C u p q hT
  have hm : 0<m := by have := u.isLt; omega
  simp only [order,Fintype.card_sum,Fintype.card_fin] at hN
  let n := m-1
  have hc : m=n+1 := by dsimp [n]; omega
  have hn : n≤10 := by omega
  have hp : p<11 := by omega
  have hq : q<11 := by omega
  obtain ⟨i,e,he⟩ := RootedCatalogueData.all_actual_trees C u hCore n hn
    (by simpa only [Fintype.card_fin] using hc)
  have hdeg : rootDegree (representative n i.val)=1 := by
    rw [representative_get,rootDegree_eq_degree,← he,e.degree_eq]
    exact hd
  have heleg : DegreeOneSmallKeys.eligible n i.val p q=true := by
    simp only [DegreeOneSmallKeys.eligible,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,hdeg⟩
  have hk := DegreeOneSmallKeys.parameter_coverage n hn i ⟨p,hp⟩ ⟨q,hq⟩ heleg
  have hcert := DegreeOneSmallKeys.all_keys_certified ⟨n,i.val,p,q⟩ hk
  change FiniteTreeTransfer.Certified (graph (representative n i.val)) (root n) p q at hcert
  rw [representative_get n i] at hcert
  have hactual : FiniteTreeTransfer.Certified C u p q :=
    certified_transport e u p q (by simpa only [he] using hcert)
  exact positive_of_certified C u p q hT (by omega) hactual
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeOneSmall
