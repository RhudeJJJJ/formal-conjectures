/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0542 : Family 10 := level10.get ⟨524,by decide⟩
def sourceMap0542 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0542 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0542_checked : acceptsGraphIso
    (source (graph core0542) (root 10) 0 0) DegreeTwoThreeSpectrum1406.graph sourceMap0542=true := by decide +kernel
theorem fusedMap0542_checked : acceptsGraphIso
    (fused (graph core0542) (root 10) 0 0) DegreeOneSmallSpectrum1019.graph fusedMap0542=true := by decide +kernel
theorem certified0542 : Certified (graph core0542) (root 10) 0 0 :=
  of_native_maps core0542 DegreeTwoThreeSpectrum1406.graph DegreeOneSmallSpectrum1019.graph
    sourceMap0542 fusedMap0542 sourceMap0542_checked fusedMap0542_checked
    DegreeTwoThreeFiniteComparisons.comparison0542
#print axioms sourceMap0542_checked
#print axioms fusedMap0542_checked
#print axioms certified0542
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
