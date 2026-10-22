/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1258 : Family 9 := level9.get ⟨244,by decide⟩
def sourceMap1258 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,11,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1258 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1258_checked : acceptsGraphIso
    (source (graph core1258) (root 9) 0 2) DegreeTwoThreeSpectrum2173.graph sourceMap1258=true := by decide +kernel
theorem fusedMap1258_checked : acceptsGraphIso
    (fused (graph core1258) (root 9) 0 2) DegreeTwoThreeSpectrum1846.graph fusedMap1258=true := by decide +kernel
theorem certified1258 : Certified (graph core1258) (root 9) 0 2 :=
  of_native_maps core1258 DegreeTwoThreeSpectrum2173.graph DegreeTwoThreeSpectrum1846.graph
    sourceMap1258 fusedMap1258 sourceMap1258_checked fusedMap1258_checked
    DegreeTwoThreeFiniteComparisons.comparison1258
#print axioms sourceMap1258_checked
#print axioms fusedMap1258_checked
#print axioms certified1258
def sourceMap1258swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,7,8,9,11] (sourceLabel 9 2 0 v)
def fusedMap1258swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1258swap_checked : acceptsGraphIso
    (source (graph core1258) (root 9) 2 0) DegreeTwoThreeSpectrum2173.graph sourceMap1258swap=true := by decide +kernel
theorem fusedMap1258swap_checked : acceptsGraphIso
    (fused (graph core1258) (root 9) 2 0) DegreeTwoThreeSpectrum1846.graph fusedMap1258swap=true := by decide +kernel
theorem certified1258swap : Certified (graph core1258) (root 9) 2 0 :=
  of_native_maps core1258 DegreeTwoThreeSpectrum2173.graph DegreeTwoThreeSpectrum1846.graph
    sourceMap1258swap fusedMap1258swap sourceMap1258swap_checked fusedMap1258swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1258
#print axioms sourceMap1258swap_checked
#print axioms fusedMap1258swap_checked
#print axioms certified1258swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
