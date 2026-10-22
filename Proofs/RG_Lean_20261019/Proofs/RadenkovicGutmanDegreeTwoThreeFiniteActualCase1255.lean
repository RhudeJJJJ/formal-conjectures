/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1255 : Family 9 := level9.get ⟨236,by decide⟩
def sourceMap1255 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1255 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1255_checked : acceptsGraphIso
    (source (graph core1255) (root 9) 0 2) DegreeTwoThreeSpectrum2164.graph sourceMap1255=true := by decide +kernel
theorem fusedMap1255_checked : acceptsGraphIso
    (fused (graph core1255) (root 9) 0 2) DegreeTwoThreeSpectrum1838.graph fusedMap1255=true := by decide +kernel
theorem certified1255 : Certified (graph core1255) (root 9) 0 2 :=
  of_native_maps core1255 DegreeTwoThreeSpectrum2164.graph DegreeTwoThreeSpectrum1838.graph
    sourceMap1255 fusedMap1255 sourceMap1255_checked fusedMap1255_checked
    DegreeTwoThreeFiniteComparisons.comparison1255
#print axioms sourceMap1255_checked
#print axioms fusedMap1255_checked
#print axioms certified1255
def sourceMap1255swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1255swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1255swap_checked : acceptsGraphIso
    (source (graph core1255) (root 9) 2 0) DegreeTwoThreeSpectrum2164.graph sourceMap1255swap=true := by decide +kernel
theorem fusedMap1255swap_checked : acceptsGraphIso
    (fused (graph core1255) (root 9) 2 0) DegreeTwoThreeSpectrum1838.graph fusedMap1255swap=true := by decide +kernel
theorem certified1255swap : Certified (graph core1255) (root 9) 2 0 :=
  of_native_maps core1255 DegreeTwoThreeSpectrum2164.graph DegreeTwoThreeSpectrum1838.graph
    sourceMap1255swap fusedMap1255swap sourceMap1255swap_checked fusedMap1255swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1255
#print axioms sourceMap1255swap_checked
#print axioms fusedMap1255swap_checked
#print axioms certified1255swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
