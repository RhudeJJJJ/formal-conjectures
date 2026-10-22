/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1837 : Family 10 := level10.get ⟨1221,by decide⟩
def sourceMap1837 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1837 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1837_checked : acceptsGraphIso
    (source (graph core1837) (root 10) 0 2) DegreeTwoThreeSpectrum3350.graph sourceMap1837=true := by decide +kernel
theorem fusedMap1837_checked : acceptsGraphIso
    (fused (graph core1837) (root 10) 0 2) DegreeTwoThreeSpectrum3349.graph fusedMap1837=true := by decide +kernel
theorem certified1837 : Certified (graph core1837) (root 10) 0 2 :=
  of_native_maps core1837 DegreeTwoThreeSpectrum3350.graph DegreeTwoThreeSpectrum3349.graph
    sourceMap1837 fusedMap1837 sourceMap1837_checked fusedMap1837_checked
    DegreeTwoThreeFiniteComparisons.comparison1837
#print axioms sourceMap1837_checked
#print axioms fusedMap1837_checked
#print axioms certified1837
def sourceMap1837swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1837swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1837swap_checked : acceptsGraphIso
    (source (graph core1837) (root 10) 2 0) DegreeTwoThreeSpectrum3350.graph sourceMap1837swap=true := by decide +kernel
theorem fusedMap1837swap_checked : acceptsGraphIso
    (fused (graph core1837) (root 10) 2 0) DegreeTwoThreeSpectrum3349.graph fusedMap1837swap=true := by decide +kernel
theorem certified1837swap : Certified (graph core1837) (root 10) 2 0 :=
  of_native_maps core1837 DegreeTwoThreeSpectrum3350.graph DegreeTwoThreeSpectrum3349.graph
    sourceMap1837swap fusedMap1837swap sourceMap1837swap_checked fusedMap1837swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1837
#print axioms sourceMap1837swap_checked
#print axioms fusedMap1837swap_checked
#print axioms certified1837swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
