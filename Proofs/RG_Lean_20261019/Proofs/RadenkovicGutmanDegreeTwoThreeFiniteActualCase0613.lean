/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0613 : Family 10 := level10.get ⟨732,by decide⟩
def sourceMap0613 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0613 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0613_checked : acceptsGraphIso
    (source (graph core0613) (root 10) 0 0) DegreeTwoThreeSpectrum1467.graph sourceMap0613=true := by decide +kernel
theorem fusedMap0613_checked : acceptsGraphIso
    (fused (graph core0613) (root 10) 0 0) DegreeOneSmallSpectrum1356.graph fusedMap0613=true := by decide +kernel
theorem certified0613 : Certified (graph core0613) (root 10) 0 0 :=
  of_native_maps core0613 DegreeTwoThreeSpectrum1467.graph DegreeOneSmallSpectrum1356.graph
    sourceMap0613 fusedMap0613 sourceMap0613_checked fusedMap0613_checked
    DegreeTwoThreeFiniteComparisons.comparison0613
#print axioms sourceMap0613_checked
#print axioms fusedMap0613_checked
#print axioms certified0613
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
