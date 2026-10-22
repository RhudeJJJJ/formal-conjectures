/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1001 : Family 10 := level10.get ⟨1717,by decide⟩
def sourceMap1001 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1001 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1001_checked : acceptsGraphIso
    (source (graph core1001) (root 10) 0 0) DegreeOneSmallSpectrum1910.graph sourceMap1001=true := by decide +kernel
theorem fusedMap1001_checked : acceptsGraphIso
    (fused (graph core1001) (root 10) 0 0) DegreeOneSmallSpectrum1909.graph fusedMap1001=true := by decide +kernel
theorem certified1001 : Certified (graph core1001) (root 10) 0 0 :=
  of_native_maps core1001 DegreeOneSmallSpectrum1910.graph DegreeOneSmallSpectrum1909.graph
    sourceMap1001 fusedMap1001 sourceMap1001_checked fusedMap1001_checked
    DegreeTwoThreeFiniteComparisons.comparison1001
#print axioms sourceMap1001_checked
#print axioms fusedMap1001_checked
#print axioms certified1001
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
