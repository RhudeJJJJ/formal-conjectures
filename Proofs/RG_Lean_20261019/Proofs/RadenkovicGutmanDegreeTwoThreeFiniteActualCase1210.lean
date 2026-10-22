/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1210 : Family 9 := level9.get ⟨90,by decide⟩
def sourceMap1210 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1210 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1210_checked : acceptsGraphIso
    (source (graph core1210) (root 9) 0 2) DegreeTwoThreeSpectrum1852.graph sourceMap1210=true := by decide +kernel
theorem fusedMap1210_checked : acceptsGraphIso
    (fused (graph core1210) (root 9) 0 2) DegreeTwoThreeSpectrum1857.graph fusedMap1210=true := by decide +kernel
theorem certified1210 : Certified (graph core1210) (root 9) 0 2 :=
  of_native_maps core1210 DegreeTwoThreeSpectrum1852.graph DegreeTwoThreeSpectrum1857.graph
    sourceMap1210 fusedMap1210 sourceMap1210_checked fusedMap1210_checked
    DegreeTwoThreeFiniteComparisons.comparison1210
#print axioms sourceMap1210_checked
#print axioms fusedMap1210_checked
#print axioms certified1210
def sourceMap1210swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1210swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1210swap_checked : acceptsGraphIso
    (source (graph core1210) (root 9) 2 0) DegreeTwoThreeSpectrum1852.graph sourceMap1210swap=true := by decide +kernel
theorem fusedMap1210swap_checked : acceptsGraphIso
    (fused (graph core1210) (root 9) 2 0) DegreeTwoThreeSpectrum1857.graph fusedMap1210swap=true := by decide +kernel
theorem certified1210swap : Certified (graph core1210) (root 9) 2 0 :=
  of_native_maps core1210 DegreeTwoThreeSpectrum1852.graph DegreeTwoThreeSpectrum1857.graph
    sourceMap1210swap fusedMap1210swap sourceMap1210swap_checked fusedMap1210swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1210
#print axioms sourceMap1210swap_checked
#print axioms fusedMap1210swap_checked
#print axioms certified1210swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
