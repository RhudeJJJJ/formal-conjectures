/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0995 : Family 10 := level10.get ⟨1705,by decide⟩
def sourceMap0995 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0995 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0995_checked : acceptsGraphIso
    (source (graph core0995) (root 10) 0 0) DegreeOneSmallSpectrum1897.graph sourceMap0995=true := by decide +kernel
theorem fusedMap0995_checked : acceptsGraphIso
    (fused (graph core0995) (root 10) 0 0) DegreeOneSmallSpectrum1896.graph fusedMap0995=true := by decide +kernel
theorem certified0995 : Certified (graph core0995) (root 10) 0 0 :=
  of_native_maps core0995 DegreeOneSmallSpectrum1897.graph DegreeOneSmallSpectrum1896.graph
    sourceMap0995 fusedMap0995 sourceMap0995_checked fusedMap0995_checked
    DegreeTwoThreeFiniteComparisons.comparison0995
#print axioms sourceMap0995_checked
#print axioms fusedMap0995_checked
#print axioms certified0995
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
