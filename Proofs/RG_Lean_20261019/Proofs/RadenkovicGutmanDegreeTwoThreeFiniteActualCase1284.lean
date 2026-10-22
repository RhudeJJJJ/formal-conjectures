/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1284 : Family 9 := level9.get ⟨309,by decide⟩
def sourceMap1284 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1284 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1284_checked : acceptsGraphIso
    (source (graph core1284) (root 9) 0 2) DegreeTwoThreeSpectrum2042.graph sourceMap1284=true := by decide +kernel
theorem fusedMap1284_checked : acceptsGraphIso
    (fused (graph core1284) (root 9) 0 2) DegreeTwoThreeSpectrum1903.graph fusedMap1284=true := by decide +kernel
theorem certified1284 : Certified (graph core1284) (root 9) 0 2 :=
  of_native_maps core1284 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1903.graph
    sourceMap1284 fusedMap1284 sourceMap1284_checked fusedMap1284_checked
    DegreeTwoThreeFiniteComparisons.comparison1284
#print axioms sourceMap1284_checked
#print axioms fusedMap1284_checked
#print axioms certified1284
def sourceMap1284swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1284swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1284swap_checked : acceptsGraphIso
    (source (graph core1284) (root 9) 2 0) DegreeTwoThreeSpectrum2042.graph sourceMap1284swap=true := by decide +kernel
theorem fusedMap1284swap_checked : acceptsGraphIso
    (fused (graph core1284) (root 9) 2 0) DegreeTwoThreeSpectrum1903.graph fusedMap1284swap=true := by decide +kernel
theorem certified1284swap : Certified (graph core1284) (root 9) 2 0 :=
  of_native_maps core1284 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1903.graph
    sourceMap1284swap fusedMap1284swap sourceMap1284swap_checked fusedMap1284swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1284
#print axioms sourceMap1284swap_checked
#print axioms fusedMap1284swap_checked
#print axioms certified1284swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
