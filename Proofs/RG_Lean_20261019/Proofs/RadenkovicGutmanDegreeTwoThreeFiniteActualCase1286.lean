/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1286 : Family 9 := level9.get ⟨312,by decide⟩
def sourceMap1286 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,5,6,7,8,9,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1286 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1286_checked : acceptsGraphIso
    (source (graph core1286) (root 9) 0 2) DegreeTwoThreeSpectrum2193.graph sourceMap1286=true := by decide +kernel
theorem fusedMap1286_checked : acceptsGraphIso
    (fused (graph core1286) (root 9) 0 2) DegreeTwoThreeSpectrum1908.graph fusedMap1286=true := by decide +kernel
theorem certified1286 : Certified (graph core1286) (root 9) 0 2 :=
  of_native_maps core1286 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1908.graph
    sourceMap1286 fusedMap1286 sourceMap1286_checked fusedMap1286_checked
    DegreeTwoThreeFiniteComparisons.comparison1286
#print axioms sourceMap1286_checked
#print axioms fusedMap1286_checked
#print axioms certified1286
def sourceMap1286swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,5,6,7,8,2,3,4,9] (sourceLabel 9 2 0 v)
def fusedMap1286swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1286swap_checked : acceptsGraphIso
    (source (graph core1286) (root 9) 2 0) DegreeTwoThreeSpectrum2193.graph sourceMap1286swap=true := by decide +kernel
theorem fusedMap1286swap_checked : acceptsGraphIso
    (fused (graph core1286) (root 9) 2 0) DegreeTwoThreeSpectrum1908.graph fusedMap1286swap=true := by decide +kernel
theorem certified1286swap : Certified (graph core1286) (root 9) 2 0 :=
  of_native_maps core1286 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1908.graph
    sourceMap1286swap fusedMap1286swap sourceMap1286swap_checked fusedMap1286swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1286
#print axioms sourceMap1286swap_checked
#print axioms fusedMap1286swap_checked
#print axioms certified1286swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
