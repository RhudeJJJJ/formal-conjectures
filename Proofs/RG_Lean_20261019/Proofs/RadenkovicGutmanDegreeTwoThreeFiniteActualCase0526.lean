/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0526 : Family 10 := level10.get ⟨477,by decide⟩
def sourceMap0526 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0526 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0526_checked : acceptsGraphIso
    (source (graph core0526) (root 10) 0 0) DegreeOneSmallSpectrum1010.graph sourceMap0526=true := by decide +kernel
theorem fusedMap0526_checked : acceptsGraphIso
    (fused (graph core0526) (root 10) 0 0) DegreeOneSmallSpectrum1408.graph fusedMap0526=true := by decide +kernel
theorem certified0526 : Certified (graph core0526) (root 10) 0 0 :=
  of_native_maps core0526 DegreeOneSmallSpectrum1010.graph DegreeOneSmallSpectrum1408.graph
    sourceMap0526 fusedMap0526 sourceMap0526_checked fusedMap0526_checked
    DegreeTwoThreeFiniteComparisons.comparison0526
#print axioms sourceMap0526_checked
#print axioms fusedMap0526_checked
#print axioms certified0526
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
