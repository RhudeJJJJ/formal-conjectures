/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0703 : Family 10 := level10.get ⟨966,by decide⟩
def sourceMap0703 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0703 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0703_checked : acceptsGraphIso
    (source (graph core0703) (root 10) 0 0) DegreeOneSmallSpectrum973.graph sourceMap0703=true := by decide +kernel
theorem fusedMap0703_checked : acceptsGraphIso
    (fused (graph core0703) (root 10) 0 0) DegreeOneSmallSpectrum970.graph fusedMap0703=true := by decide +kernel
theorem certified0703 : Certified (graph core0703) (root 10) 0 0 :=
  of_native_maps core0703 DegreeOneSmallSpectrum973.graph DegreeOneSmallSpectrum970.graph
    sourceMap0703 fusedMap0703 sourceMap0703_checked fusedMap0703_checked
    DegreeTwoThreeFiniteComparisons.comparison0703
#print axioms sourceMap0703_checked
#print axioms fusedMap0703_checked
#print axioms certified0703
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
