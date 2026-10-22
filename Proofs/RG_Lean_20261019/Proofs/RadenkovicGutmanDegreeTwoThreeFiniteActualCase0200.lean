/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0200 : Family 9 := level9.get ⟨164,by decide⟩
def sourceMap0200 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0200 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0200_checked : acceptsGraphIso
    (source (graph core0200) (root 9) 0 0) DegreeOneSmallSpectrum662.graph sourceMap0200=true := by decide +kernel
theorem fusedMap0200_checked : acceptsGraphIso
    (fused (graph core0200) (root 9) 0 0) DegreeOneSmallSpectrum438.graph fusedMap0200=true := by decide +kernel
theorem certified0200 : Certified (graph core0200) (root 9) 0 0 :=
  of_native_maps core0200 DegreeOneSmallSpectrum662.graph DegreeOneSmallSpectrum438.graph
    sourceMap0200 fusedMap0200 sourceMap0200_checked fusedMap0200_checked
    DegreeTwoThreeFiniteComparisons.comparison0200
#print axioms sourceMap0200_checked
#print axioms fusedMap0200_checked
#print axioms certified0200
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
