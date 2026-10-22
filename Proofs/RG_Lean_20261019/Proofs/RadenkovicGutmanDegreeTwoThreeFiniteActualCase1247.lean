/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1247 : Family 9 := level9.get ⟨210,by decide⟩
def sourceMap1247 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1247 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1247_checked : acceptsGraphIso
    (source (graph core1247) (root 9) 0 2) DegreeTwoThreeSpectrum2109.graph sourceMap1247=true := by decide +kernel
theorem fusedMap1247_checked : acceptsGraphIso
    (fused (graph core1247) (root 9) 0 2) DegreeTwoThreeSpectrum1813.graph fusedMap1247=true := by decide +kernel
theorem certified1247 : Certified (graph core1247) (root 9) 0 2 :=
  of_native_maps core1247 DegreeTwoThreeSpectrum2109.graph DegreeTwoThreeSpectrum1813.graph
    sourceMap1247 fusedMap1247 sourceMap1247_checked fusedMap1247_checked
    DegreeTwoThreeFiniteComparisons.comparison1247
#print axioms sourceMap1247_checked
#print axioms fusedMap1247_checked
#print axioms certified1247
def sourceMap1247swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1247swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1247swap_checked : acceptsGraphIso
    (source (graph core1247) (root 9) 2 0) DegreeTwoThreeSpectrum2109.graph sourceMap1247swap=true := by decide +kernel
theorem fusedMap1247swap_checked : acceptsGraphIso
    (fused (graph core1247) (root 9) 2 0) DegreeTwoThreeSpectrum1813.graph fusedMap1247swap=true := by decide +kernel
theorem certified1247swap : Certified (graph core1247) (root 9) 2 0 :=
  of_native_maps core1247 DegreeTwoThreeSpectrum2109.graph DegreeTwoThreeSpectrum1813.graph
    sourceMap1247swap fusedMap1247swap sourceMap1247swap_checked fusedMap1247swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1247
#print axioms sourceMap1247swap_checked
#print axioms fusedMap1247swap_checked
#print axioms certified1247swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
