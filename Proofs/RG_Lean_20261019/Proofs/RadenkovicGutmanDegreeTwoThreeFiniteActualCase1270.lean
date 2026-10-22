/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1270 : Family 9 := level9.get ⟨278,by decide⟩
def sourceMap1270 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1270 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1270_checked : acceptsGraphIso
    (source (graph core1270) (root 9) 0 2) DegreeTwoThreeSpectrum2223.graph sourceMap1270=true := by decide +kernel
theorem fusedMap1270_checked : acceptsGraphIso
    (fused (graph core1270) (root 9) 0 2) DegreeTwoThreeSpectrum1891.graph fusedMap1270=true := by decide +kernel
theorem certified1270 : Certified (graph core1270) (root 9) 0 2 :=
  of_native_maps core1270 DegreeTwoThreeSpectrum2223.graph DegreeTwoThreeSpectrum1891.graph
    sourceMap1270 fusedMap1270 sourceMap1270_checked fusedMap1270_checked
    DegreeTwoThreeFiniteComparisons.comparison1270
#print axioms sourceMap1270_checked
#print axioms fusedMap1270_checked
#print axioms certified1270
def sourceMap1270swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1270swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1270swap_checked : acceptsGraphIso
    (source (graph core1270) (root 9) 2 0) DegreeTwoThreeSpectrum2223.graph sourceMap1270swap=true := by decide +kernel
theorem fusedMap1270swap_checked : acceptsGraphIso
    (fused (graph core1270) (root 9) 2 0) DegreeTwoThreeSpectrum1891.graph fusedMap1270swap=true := by decide +kernel
theorem certified1270swap : Certified (graph core1270) (root 9) 2 0 :=
  of_native_maps core1270 DegreeTwoThreeSpectrum2223.graph DegreeTwoThreeSpectrum1891.graph
    sourceMap1270swap fusedMap1270swap sourceMap1270swap_checked fusedMap1270swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1270
#print axioms sourceMap1270swap_checked
#print axioms fusedMap1270swap_checked
#print axioms certified1270swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
