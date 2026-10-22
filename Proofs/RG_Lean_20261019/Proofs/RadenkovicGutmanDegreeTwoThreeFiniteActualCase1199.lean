/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1199 : Family 9 := level9.get ⟨41,by decide⟩
def sourceMap1199 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,9,10,11,12,13,6,7,8,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1199 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1199_checked : acceptsGraphIso
    (source (graph core1199) (root 9) 0 2) DegreeTwoThreeSpectrum1870.graph sourceMap1199=true := by decide +kernel
theorem fusedMap1199_checked : acceptsGraphIso
    (fused (graph core1199) (root 9) 0 2) DegreeTwoThreeSpectrum1729.graph fusedMap1199=true := by decide +kernel
theorem certified1199 : Certified (graph core1199) (root 9) 0 2 :=
  of_native_maps core1199 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap1199 fusedMap1199 sourceMap1199_checked fusedMap1199_checked
    DegreeTwoThreeFiniteComparisons.comparison1199
#print axioms sourceMap1199_checked
#print axioms fusedMap1199_checked
#print axioms certified1199
def sourceMap1199swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,9,10,11,12,13,6,7,3,4,5,8] (sourceLabel 9 2 0 v)
def fusedMap1199swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1199swap_checked : acceptsGraphIso
    (source (graph core1199) (root 9) 2 0) DegreeTwoThreeSpectrum1870.graph sourceMap1199swap=true := by decide +kernel
theorem fusedMap1199swap_checked : acceptsGraphIso
    (fused (graph core1199) (root 9) 2 0) DegreeTwoThreeSpectrum1729.graph fusedMap1199swap=true := by decide +kernel
theorem certified1199swap : Certified (graph core1199) (root 9) 2 0 :=
  of_native_maps core1199 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap1199swap fusedMap1199swap sourceMap1199swap_checked fusedMap1199swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1199
#print axioms sourceMap1199swap_checked
#print axioms fusedMap1199swap_checked
#print axioms certified1199swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
