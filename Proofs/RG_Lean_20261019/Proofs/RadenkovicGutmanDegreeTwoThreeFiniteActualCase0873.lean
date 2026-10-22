/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0873 : Family 10 := level10.get ⟨1380,by decide⟩
def sourceMap0873 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0873 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0873_checked : acceptsGraphIso
    (source (graph core0873) (root 10) 0 0) DegreeOneSmallSpectrum1419.graph sourceMap0873=true := by decide +kernel
theorem fusedMap0873_checked : acceptsGraphIso
    (fused (graph core0873) (root 10) 0 0) DegreeOneSmallSpectrum1409.graph fusedMap0873=true := by decide +kernel
theorem certified0873 : Certified (graph core0873) (root 10) 0 0 :=
  of_native_maps core0873 DegreeOneSmallSpectrum1419.graph DegreeOneSmallSpectrum1409.graph
    sourceMap0873 fusedMap0873 sourceMap0873_checked fusedMap0873_checked
    DegreeTwoThreeFiniteComparisons.comparison0873
#print axioms sourceMap0873_checked
#print axioms fusedMap0873_checked
#print axioms certified0873
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
