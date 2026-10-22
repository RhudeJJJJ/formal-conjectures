/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1278 : Family 9 := level9.get ⟨298,by decide⟩
def sourceMap1278 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1278 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,5,6,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1278_checked : acceptsGraphIso
    (source (graph core1278) (root 9) 0 2) DegreeTwoThreeSpectrum2213.graph sourceMap1278=true := by decide +kernel
theorem fusedMap1278_checked : acceptsGraphIso
    (fused (graph core1278) (root 9) 0 2) DegreeTwoThreeSpectrum1915.graph fusedMap1278=true := by decide +kernel
theorem certified1278 : Certified (graph core1278) (root 9) 0 2 :=
  of_native_maps core1278 DegreeTwoThreeSpectrum2213.graph DegreeTwoThreeSpectrum1915.graph
    sourceMap1278 fusedMap1278 sourceMap1278_checked fusedMap1278_checked
    DegreeTwoThreeFiniteComparisons.comparison1278
#print axioms sourceMap1278_checked
#print axioms fusedMap1278_checked
#print axioms certified1278
def sourceMap1278swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1278swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,5,6,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1278swap_checked : acceptsGraphIso
    (source (graph core1278) (root 9) 2 0) DegreeTwoThreeSpectrum2213.graph sourceMap1278swap=true := by decide +kernel
theorem fusedMap1278swap_checked : acceptsGraphIso
    (fused (graph core1278) (root 9) 2 0) DegreeTwoThreeSpectrum1915.graph fusedMap1278swap=true := by decide +kernel
theorem certified1278swap : Certified (graph core1278) (root 9) 2 0 :=
  of_native_maps core1278 DegreeTwoThreeSpectrum2213.graph DegreeTwoThreeSpectrum1915.graph
    sourceMap1278swap fusedMap1278swap sourceMap1278swap_checked fusedMap1278swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1278
#print axioms sourceMap1278swap_checked
#print axioms fusedMap1278swap_checked
#print axioms certified1278swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
