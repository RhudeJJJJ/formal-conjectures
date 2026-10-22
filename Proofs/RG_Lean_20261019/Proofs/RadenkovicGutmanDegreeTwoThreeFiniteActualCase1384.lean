/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1384 : Family 9 := level9.get ⟨563,by decide⟩
def sourceMap1384 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1384 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1384_checked : acceptsGraphIso
    (source (graph core1384) (root 9) 0 2) DegreeTwoThreeSpectrum2255.graph sourceMap1384=true := by decide +kernel
theorem fusedMap1384_checked : acceptsGraphIso
    (fused (graph core1384) (root 9) 0 2) DegreeTwoThreeSpectrum1949.graph fusedMap1384=true := by decide +kernel
theorem certified1384 : Certified (graph core1384) (root 9) 0 2 :=
  of_native_maps core1384 DegreeTwoThreeSpectrum2255.graph DegreeTwoThreeSpectrum1949.graph
    sourceMap1384 fusedMap1384 sourceMap1384_checked fusedMap1384_checked
    DegreeTwoThreeFiniteComparisons.comparison1384
#print axioms sourceMap1384_checked
#print axioms fusedMap1384_checked
#print axioms certified1384
def sourceMap1384swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1384swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1384swap_checked : acceptsGraphIso
    (source (graph core1384) (root 9) 2 0) DegreeTwoThreeSpectrum2255.graph sourceMap1384swap=true := by decide +kernel
theorem fusedMap1384swap_checked : acceptsGraphIso
    (fused (graph core1384) (root 9) 2 0) DegreeTwoThreeSpectrum1949.graph fusedMap1384swap=true := by decide +kernel
theorem certified1384swap : Certified (graph core1384) (root 9) 2 0 :=
  of_native_maps core1384 DegreeTwoThreeSpectrum2255.graph DegreeTwoThreeSpectrum1949.graph
    sourceMap1384swap fusedMap1384swap sourceMap1384swap_checked fusedMap1384swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1384
#print axioms sourceMap1384swap_checked
#print axioms fusedMap1384swap_checked
#print axioms certified1384swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
