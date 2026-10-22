/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0475 : Family 10 := level10.get ⟨317,by decide⟩
def sourceMap0475 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0475 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0475_checked : acceptsGraphIso
    (source (graph core0475) (root 10) 0 0) DegreeTwoThreeSpectrum895.graph sourceMap0475=true := by decide +kernel
theorem fusedMap0475_checked : acceptsGraphIso
    (fused (graph core0475) (root 10) 0 0) DegreeOneSmallSpectrum1384.graph fusedMap0475=true := by decide +kernel
theorem certified0475 : Certified (graph core0475) (root 10) 0 0 :=
  of_native_maps core0475 DegreeTwoThreeSpectrum895.graph DegreeOneSmallSpectrum1384.graph
    sourceMap0475 fusedMap0475 sourceMap0475_checked fusedMap0475_checked
    DegreeTwoThreeFiniteComparisons.comparison0475
#print axioms sourceMap0475_checked
#print axioms fusedMap0475_checked
#print axioms certified0475
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
