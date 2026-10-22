/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0718 : Family 10 := level10.get ⟨1005,by decide⟩
def sourceMap0718 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0718 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0718_checked : acceptsGraphIso
    (source (graph core0718) (root 10) 0 0) DegreeTwoThreeSpectrum1299.graph sourceMap0718=true := by decide +kernel
theorem fusedMap0718_checked : acceptsGraphIso
    (fused (graph core0718) (root 10) 0 0) DegreeOneSmallSpectrum1551.graph fusedMap0718=true := by decide +kernel
theorem certified0718 : Certified (graph core0718) (root 10) 0 0 :=
  of_native_maps core0718 DegreeTwoThreeSpectrum1299.graph DegreeOneSmallSpectrum1551.graph
    sourceMap0718 fusedMap0718 sourceMap0718_checked fusedMap0718_checked
    DegreeTwoThreeFiniteComparisons.comparison0718
#print axioms sourceMap0718_checked
#print axioms fusedMap0718_checked
#print axioms certified0718
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
