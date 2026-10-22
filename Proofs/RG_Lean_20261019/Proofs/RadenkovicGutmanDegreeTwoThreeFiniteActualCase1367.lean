/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1367 : Family 9 := level9.get ⟨517,by decide⟩
def sourceMap1367 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1367 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1367_checked : acceptsGraphIso
    (source (graph core1367) (root 9) 0 2) DegreeTwoThreeSpectrum2232.graph sourceMap1367=true := by decide +kernel
theorem fusedMap1367_checked : acceptsGraphIso
    (fused (graph core1367) (root 9) 0 2) DegreeTwoThreeSpectrum2229.graph fusedMap1367=true := by decide +kernel
theorem certified1367 : Certified (graph core1367) (root 9) 0 2 :=
  of_native_maps core1367 DegreeTwoThreeSpectrum2232.graph DegreeTwoThreeSpectrum2229.graph
    sourceMap1367 fusedMap1367 sourceMap1367_checked fusedMap1367_checked
    DegreeTwoThreeFiniteComparisons.comparison1367
#print axioms sourceMap1367_checked
#print axioms fusedMap1367_checked
#print axioms certified1367
def sourceMap1367swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1367swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1367swap_checked : acceptsGraphIso
    (source (graph core1367) (root 9) 2 0) DegreeTwoThreeSpectrum2232.graph sourceMap1367swap=true := by decide +kernel
theorem fusedMap1367swap_checked : acceptsGraphIso
    (fused (graph core1367) (root 9) 2 0) DegreeTwoThreeSpectrum2229.graph fusedMap1367swap=true := by decide +kernel
theorem certified1367swap : Certified (graph core1367) (root 9) 2 0 :=
  of_native_maps core1367 DegreeTwoThreeSpectrum2232.graph DegreeTwoThreeSpectrum2229.graph
    sourceMap1367swap fusedMap1367swap sourceMap1367swap_checked fusedMap1367swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1367
#print axioms sourceMap1367swap_checked
#print axioms fusedMap1367swap_checked
#print axioms certified1367swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
