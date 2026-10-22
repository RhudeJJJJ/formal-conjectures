/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1264 : Family 9 := level9.get ⟨261,by decide⟩
def sourceMap1264 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1264 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1264_checked : acceptsGraphIso
    (source (graph core1264) (root 9) 0 2) DegreeTwoThreeSpectrum2211.graph sourceMap1264=true := by decide +kernel
theorem fusedMap1264_checked : acceptsGraphIso
    (fused (graph core1264) (root 9) 0 2) DegreeTwoThreeSpectrum1869.graph fusedMap1264=true := by decide +kernel
theorem certified1264 : Certified (graph core1264) (root 9) 0 2 :=
  of_native_maps core1264 DegreeTwoThreeSpectrum2211.graph DegreeTwoThreeSpectrum1869.graph
    sourceMap1264 fusedMap1264 sourceMap1264_checked fusedMap1264_checked
    DegreeTwoThreeFiniteComparisons.comparison1264
#print axioms sourceMap1264_checked
#print axioms fusedMap1264_checked
#print axioms certified1264
def sourceMap1264swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1264swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1264swap_checked : acceptsGraphIso
    (source (graph core1264) (root 9) 2 0) DegreeTwoThreeSpectrum2211.graph sourceMap1264swap=true := by decide +kernel
theorem fusedMap1264swap_checked : acceptsGraphIso
    (fused (graph core1264) (root 9) 2 0) DegreeTwoThreeSpectrum1869.graph fusedMap1264swap=true := by decide +kernel
theorem certified1264swap : Certified (graph core1264) (root 9) 2 0 :=
  of_native_maps core1264 DegreeTwoThreeSpectrum2211.graph DegreeTwoThreeSpectrum1869.graph
    sourceMap1264swap fusedMap1264swap sourceMap1264swap_checked fusedMap1264swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1264
#print axioms sourceMap1264swap_checked
#print axioms fusedMap1264swap_checked
#print axioms certified1264swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
