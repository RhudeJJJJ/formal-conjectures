/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0539 : Family 10 := level10.get ⟨513,by decide⟩
def sourceMap0539 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0539 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0539_checked : acceptsGraphIso
    (source (graph core0539) (root 10) 0 0) DegreeTwoThreeSpectrum1339.graph sourceMap0539=true := by decide +kernel
theorem fusedMap0539_checked : acceptsGraphIso
    (fused (graph core0539) (root 10) 0 0) DegreeOneSmallSpectrum1003.graph fusedMap0539=true := by decide +kernel
theorem certified0539 : Certified (graph core0539) (root 10) 0 0 :=
  of_native_maps core0539 DegreeTwoThreeSpectrum1339.graph DegreeOneSmallSpectrum1003.graph
    sourceMap0539 fusedMap0539 sourceMap0539_checked fusedMap0539_checked
    DegreeTwoThreeFiniteComparisons.comparison0539
#print axioms sourceMap0539_checked
#print axioms fusedMap0539_checked
#print axioms certified0539
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
