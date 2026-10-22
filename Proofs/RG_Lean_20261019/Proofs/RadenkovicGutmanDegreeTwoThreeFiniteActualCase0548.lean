/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0548 : Family 10 := level10.get ⟨544,by decide⟩
def sourceMap0548 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0548 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0548_checked : acceptsGraphIso
    (source (graph core0548) (root 10) 0 0) DegreeTwoThreeSpectrum1419.graph sourceMap0548=true := by decide +kernel
theorem fusedMap0548_checked : acceptsGraphIso
    (fused (graph core0548) (root 10) 0 0) DegreeOneSmallSpectrum1054.graph fusedMap0548=true := by decide +kernel
theorem certified0548 : Certified (graph core0548) (root 10) 0 0 :=
  of_native_maps core0548 DegreeTwoThreeSpectrum1419.graph DegreeOneSmallSpectrum1054.graph
    sourceMap0548 fusedMap0548 sourceMap0548_checked fusedMap0548_checked
    DegreeTwoThreeFiniteComparisons.comparison0548
#print axioms sourceMap0548_checked
#print axioms fusedMap0548_checked
#print axioms certified0548
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
