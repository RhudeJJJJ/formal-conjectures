/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0921 : Family 10 := level10.get ⟨1497,by decide⟩
def sourceMap0921 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0921 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0921_checked : acceptsGraphIso
    (source (graph core0921) (root 10) 0 0) DegreeOneSmallSpectrum1097.graph sourceMap0921=true := by decide +kernel
theorem fusedMap0921_checked : acceptsGraphIso
    (fused (graph core0921) (root 10) 0 0) DegreeOneSmallSpectrum1096.graph fusedMap0921=true := by decide +kernel
theorem certified0921 : Certified (graph core0921) (root 10) 0 0 :=
  of_native_maps core0921 DegreeOneSmallSpectrum1097.graph DegreeOneSmallSpectrum1096.graph
    sourceMap0921 fusedMap0921 sourceMap0921_checked fusedMap0921_checked
    DegreeTwoThreeFiniteComparisons.comparison0921
#print axioms sourceMap0921_checked
#print axioms fusedMap0921_checked
#print axioms certified0921
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
