/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1279 : Family 9 := level9.get ⟨301,by decide⟩
def sourceMap1279 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1279 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1279_checked : acceptsGraphIso
    (source (graph core1279) (root 9) 0 2) DegreeTwoThreeSpectrum2228.graph sourceMap1279=true := by decide +kernel
theorem fusedMap1279_checked : acceptsGraphIso
    (fused (graph core1279) (root 9) 0 2) DegreeTwoThreeSpectrum1919.graph fusedMap1279=true := by decide +kernel
theorem certified1279 : Certified (graph core1279) (root 9) 0 2 :=
  of_native_maps core1279 DegreeTwoThreeSpectrum2228.graph DegreeTwoThreeSpectrum1919.graph
    sourceMap1279 fusedMap1279 sourceMap1279_checked fusedMap1279_checked
    DegreeTwoThreeFiniteComparisons.comparison1279
#print axioms sourceMap1279_checked
#print axioms fusedMap1279_checked
#print axioms certified1279
def sourceMap1279swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1279swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1279swap_checked : acceptsGraphIso
    (source (graph core1279) (root 9) 2 0) DegreeTwoThreeSpectrum2228.graph sourceMap1279swap=true := by decide +kernel
theorem fusedMap1279swap_checked : acceptsGraphIso
    (fused (graph core1279) (root 9) 2 0) DegreeTwoThreeSpectrum1919.graph fusedMap1279swap=true := by decide +kernel
theorem certified1279swap : Certified (graph core1279) (root 9) 2 0 :=
  of_native_maps core1279 DegreeTwoThreeSpectrum2228.graph DegreeTwoThreeSpectrum1919.graph
    sourceMap1279swap fusedMap1279swap sourceMap1279swap_checked fusedMap1279swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1279
#print axioms sourceMap1279swap_checked
#print axioms fusedMap1279swap_checked
#print axioms certified1279swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
