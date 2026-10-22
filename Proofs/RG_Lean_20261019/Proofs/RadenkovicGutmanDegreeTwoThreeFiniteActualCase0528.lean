/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0528 : Family 10 := level10.get ⟨481,by decide⟩
def sourceMap0528 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0528 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0528_checked : acceptsGraphIso
    (source (graph core0528) (root 10) 0 0) DegreeOneSmallSpectrum1016.graph sourceMap0528=true := by decide +kernel
theorem fusedMap0528_checked : acceptsGraphIso
    (fused (graph core0528) (root 10) 0 0) DegreeOneSmallSpectrum1418.graph fusedMap0528=true := by decide +kernel
theorem certified0528 : Certified (graph core0528) (root 10) 0 0 :=
  of_native_maps core0528 DegreeOneSmallSpectrum1016.graph DegreeOneSmallSpectrum1418.graph
    sourceMap0528 fusedMap0528 sourceMap0528_checked fusedMap0528_checked
    DegreeTwoThreeFiniteComparisons.comparison0528
#print axioms sourceMap0528_checked
#print axioms fusedMap0528_checked
#print axioms certified0528
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
