/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0851 : Family 10 := level10.get ⟨1333,by decide⟩
def sourceMap0851 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0851 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0851_checked : acceptsGraphIso
    (source (graph core0851) (root 10) 0 0) DegreeOneSmallSpectrum1804.graph sourceMap0851=true := by decide +kernel
theorem fusedMap0851_checked : acceptsGraphIso
    (fused (graph core0851) (root 10) 0 0) DegreeOneSmallSpectrum1767.graph fusedMap0851=true := by decide +kernel
theorem certified0851 : Certified (graph core0851) (root 10) 0 0 :=
  of_native_maps core0851 DegreeOneSmallSpectrum1804.graph DegreeOneSmallSpectrum1767.graph
    sourceMap0851 fusedMap0851 sourceMap0851_checked fusedMap0851_checked
    DegreeTwoThreeFiniteComparisons.comparison0851
#print axioms sourceMap0851_checked
#print axioms fusedMap0851_checked
#print axioms certified0851
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
