/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0601 : Family 10 := level10.get ⟨697,by decide⟩
def sourceMap0601 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0601 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0601_checked : acceptsGraphIso
    (source (graph core0601) (root 10) 0 0) DegreeTwoThreeSpectrum1430.graph sourceMap0601=true := by decide +kernel
theorem fusedMap0601_checked : acceptsGraphIso
    (fused (graph core0601) (root 10) 0 0) DegreeOneSmallSpectrum1308.graph fusedMap0601=true := by decide +kernel
theorem certified0601 : Certified (graph core0601) (root 10) 0 0 :=
  of_native_maps core0601 DegreeTwoThreeSpectrum1430.graph DegreeOneSmallSpectrum1308.graph
    sourceMap0601 fusedMap0601 sourceMap0601_checked fusedMap0601_checked
    DegreeTwoThreeFiniteComparisons.comparison0601
#print axioms sourceMap0601_checked
#print axioms fusedMap0601_checked
#print axioms certified0601
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
