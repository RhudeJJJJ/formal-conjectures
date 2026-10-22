/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1297 : Family 9 := level9.get ⟨348,by decide⟩
def sourceMap1297 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1297 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1297_checked : acceptsGraphIso
    (source (graph core1297) (root 9) 0 2) DegreeTwoThreeSpectrum1978.graph sourceMap1297=true := by decide +kernel
theorem fusedMap1297_checked : acceptsGraphIso
    (fused (graph core1297) (root 9) 0 2) DegreeTwoThreeSpectrum1980.graph fusedMap1297=true := by decide +kernel
theorem certified1297 : Certified (graph core1297) (root 9) 0 2 :=
  of_native_maps core1297 DegreeTwoThreeSpectrum1978.graph DegreeTwoThreeSpectrum1980.graph
    sourceMap1297 fusedMap1297 sourceMap1297_checked fusedMap1297_checked
    DegreeTwoThreeFiniteComparisons.comparison1297
#print axioms sourceMap1297_checked
#print axioms fusedMap1297_checked
#print axioms certified1297
def sourceMap1297swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1297swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1297swap_checked : acceptsGraphIso
    (source (graph core1297) (root 9) 2 0) DegreeTwoThreeSpectrum1978.graph sourceMap1297swap=true := by decide +kernel
theorem fusedMap1297swap_checked : acceptsGraphIso
    (fused (graph core1297) (root 9) 2 0) DegreeTwoThreeSpectrum1980.graph fusedMap1297swap=true := by decide +kernel
theorem certified1297swap : Certified (graph core1297) (root 9) 2 0 :=
  of_native_maps core1297 DegreeTwoThreeSpectrum1978.graph DegreeTwoThreeSpectrum1980.graph
    sourceMap1297swap fusedMap1297swap sourceMap1297swap_checked fusedMap1297swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1297
#print axioms sourceMap1297swap_checked
#print axioms fusedMap1297swap_checked
#print axioms certified1297swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
