/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0037 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap0037 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0037 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0037_checked : acceptsGraphIso
    (source (graph core0037) (root 7) 0 0) DegreeOneSmallSpectrum104.graph sourceMap0037=true := by decide +kernel
theorem fusedMap0037_checked : acceptsGraphIso
    (fused (graph core0037) (root 7) 0 0) DegreeOneSmallSpectrum136.graph fusedMap0037=true := by decide +kernel
theorem certified0037 : Certified (graph core0037) (root 7) 0 0 :=
  of_native_maps core0037 DegreeOneSmallSpectrum104.graph DegreeOneSmallSpectrum136.graph
    sourceMap0037 fusedMap0037 sourceMap0037_checked fusedMap0037_checked
    DegreeTwoThreeFiniteComparisons.comparison0037
#print axioms sourceMap0037_checked
#print axioms fusedMap0037_checked
#print axioms certified0037
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
