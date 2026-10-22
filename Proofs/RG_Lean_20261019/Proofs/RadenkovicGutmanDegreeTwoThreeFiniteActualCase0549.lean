/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0549 : Family 10 := level10.get ⟨545,by decide⟩
def sourceMap0549 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0549 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0549_checked : acceptsGraphIso
    (source (graph core0549) (root 10) 0 0) DegreeTwoThreeSpectrum895.graph sourceMap0549=true := by decide +kernel
theorem fusedMap0549_checked : acceptsGraphIso
    (fused (graph core0549) (root 10) 0 0) DegreeOneSmallSpectrum1053.graph fusedMap0549=true := by decide +kernel
theorem certified0549 : Certified (graph core0549) (root 10) 0 0 :=
  of_native_maps core0549 DegreeTwoThreeSpectrum895.graph DegreeOneSmallSpectrum1053.graph
    sourceMap0549 fusedMap0549 sourceMap0549_checked fusedMap0549_checked
    DegreeTwoThreeFiniteComparisons.comparison0549
#print axioms sourceMap0549_checked
#print axioms fusedMap0549_checked
#print axioms certified0549
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
