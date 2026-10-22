/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0503 : Family 10 := level10.get ⟨410,by decide⟩
def sourceMap0503 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0503 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0503_checked : acceptsGraphIso
    (source (graph core0503) (root 10) 0 0) DegreeOneSmallSpectrum1048.graph sourceMap0503=true := by decide +kernel
theorem fusedMap0503_checked : acceptsGraphIso
    (fused (graph core0503) (root 10) 0 0) DegreeOneSmallSpectrum1451.graph fusedMap0503=true := by decide +kernel
theorem certified0503 : Certified (graph core0503) (root 10) 0 0 :=
  of_native_maps core0503 DegreeOneSmallSpectrum1048.graph DegreeOneSmallSpectrum1451.graph
    sourceMap0503 fusedMap0503 sourceMap0503_checked fusedMap0503_checked
    DegreeTwoThreeFiniteComparisons.comparison0503
#print axioms sourceMap0503_checked
#print axioms fusedMap0503_checked
#print axioms certified0503
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
