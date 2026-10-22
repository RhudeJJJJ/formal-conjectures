/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1012 : Family 10 := level10.get ⟨1751,by decide⟩
def sourceMap1012 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1012 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1012_checked : acceptsGraphIso
    (source (graph core1012) (root 10) 0 0) DegreeTwoThreeSpectrum1644.graph sourceMap1012=true := by decide +kernel
theorem fusedMap1012_checked : acceptsGraphIso
    (fused (graph core1012) (root 10) 0 0) DegreeTwoThreeSpectrum1643.graph fusedMap1012=true := by decide +kernel
theorem certified1012 : Certified (graph core1012) (root 10) 0 0 :=
  of_native_maps core1012 DegreeTwoThreeSpectrum1644.graph DegreeTwoThreeSpectrum1643.graph
    sourceMap1012 fusedMap1012 sourceMap1012_checked fusedMap1012_checked
    DegreeTwoThreeFiniteComparisons.comparison1012
#print axioms sourceMap1012_checked
#print axioms fusedMap1012_checked
#print axioms certified1012
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
