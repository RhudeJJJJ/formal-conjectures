/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1830 : Family 10 := level10.get ⟨1206,by decide⟩
def sourceMap1830 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1830 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1830_checked : acceptsGraphIso
    (source (graph core1830) (root 10) 0 2) DegreeTwoThreeSpectrum3327.graph sourceMap1830=true := by decide +kernel
theorem fusedMap1830_checked : acceptsGraphIso
    (fused (graph core1830) (root 10) 0 2) DegreeTwoThreeSpectrum3329.graph fusedMap1830=true := by decide +kernel
theorem certified1830 : Certified (graph core1830) (root 10) 0 2 :=
  of_native_maps core1830 DegreeTwoThreeSpectrum3327.graph DegreeTwoThreeSpectrum3329.graph
    sourceMap1830 fusedMap1830 sourceMap1830_checked fusedMap1830_checked
    DegreeTwoThreeFiniteComparisons.comparison1830
#print axioms sourceMap1830_checked
#print axioms fusedMap1830_checked
#print axioms certified1830
def sourceMap1830swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1830swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1830swap_checked : acceptsGraphIso
    (source (graph core1830) (root 10) 2 0) DegreeTwoThreeSpectrum3327.graph sourceMap1830swap=true := by decide +kernel
theorem fusedMap1830swap_checked : acceptsGraphIso
    (fused (graph core1830) (root 10) 2 0) DegreeTwoThreeSpectrum3329.graph fusedMap1830swap=true := by decide +kernel
theorem certified1830swap : Certified (graph core1830) (root 10) 2 0 :=
  of_native_maps core1830 DegreeTwoThreeSpectrum3327.graph DegreeTwoThreeSpectrum3329.graph
    sourceMap1830swap fusedMap1830swap sourceMap1830swap_checked fusedMap1830swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1830
#print axioms sourceMap1830swap_checked
#print axioms fusedMap1830swap_checked
#print axioms certified1830swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
