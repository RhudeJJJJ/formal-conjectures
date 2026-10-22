/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1294 : Family 9 := level9.get ⟨340,by decide⟩
def sourceMap1294 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1294 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1294_checked : acceptsGraphIso
    (source (graph core1294) (root 9) 0 2) DegreeTwoThreeSpectrum1966.graph sourceMap1294=true := by decide +kernel
theorem fusedMap1294_checked : acceptsGraphIso
    (fused (graph core1294) (root 9) 0 2) DegreeTwoThreeSpectrum1968.graph fusedMap1294=true := by decide +kernel
theorem certified1294 : Certified (graph core1294) (root 9) 0 2 :=
  of_native_maps core1294 DegreeTwoThreeSpectrum1966.graph DegreeTwoThreeSpectrum1968.graph
    sourceMap1294 fusedMap1294 sourceMap1294_checked fusedMap1294_checked
    DegreeTwoThreeFiniteComparisons.comparison1294
#print axioms sourceMap1294_checked
#print axioms fusedMap1294_checked
#print axioms certified1294
def sourceMap1294swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1294swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1294swap_checked : acceptsGraphIso
    (source (graph core1294) (root 9) 2 0) DegreeTwoThreeSpectrum1966.graph sourceMap1294swap=true := by decide +kernel
theorem fusedMap1294swap_checked : acceptsGraphIso
    (fused (graph core1294) (root 9) 2 0) DegreeTwoThreeSpectrum1968.graph fusedMap1294swap=true := by decide +kernel
theorem certified1294swap : Certified (graph core1294) (root 9) 2 0 :=
  of_native_maps core1294 DegreeTwoThreeSpectrum1966.graph DegreeTwoThreeSpectrum1968.graph
    sourceMap1294swap fusedMap1294swap sourceMap1294swap_checked fusedMap1294swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1294
#print axioms sourceMap1294swap_checked
#print axioms fusedMap1294swap_checked
#print axioms certified1294swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
