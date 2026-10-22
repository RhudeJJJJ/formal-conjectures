/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1381 : Family 9 := level9.get ⟨555,by decide⟩
def sourceMap1381 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1381 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1381_checked : acceptsGraphIso
    (source (graph core1381) (root 9) 0 2) DegreeTwoThreeSpectrum2252.graph sourceMap1381=true := by decide +kernel
theorem fusedMap1381_checked : acceptsGraphIso
    (fused (graph core1381) (root 9) 0 2) DegreeTwoThreeSpectrum1937.graph fusedMap1381=true := by decide +kernel
theorem certified1381 : Certified (graph core1381) (root 9) 0 2 :=
  of_native_maps core1381 DegreeTwoThreeSpectrum2252.graph DegreeTwoThreeSpectrum1937.graph
    sourceMap1381 fusedMap1381 sourceMap1381_checked fusedMap1381_checked
    DegreeTwoThreeFiniteComparisons.comparison1381
#print axioms sourceMap1381_checked
#print axioms fusedMap1381_checked
#print axioms certified1381
def sourceMap1381swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1381swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1381swap_checked : acceptsGraphIso
    (source (graph core1381) (root 9) 2 0) DegreeTwoThreeSpectrum2252.graph sourceMap1381swap=true := by decide +kernel
theorem fusedMap1381swap_checked : acceptsGraphIso
    (fused (graph core1381) (root 9) 2 0) DegreeTwoThreeSpectrum1937.graph fusedMap1381swap=true := by decide +kernel
theorem certified1381swap : Certified (graph core1381) (root 9) 2 0 :=
  of_native_maps core1381 DegreeTwoThreeSpectrum2252.graph DegreeTwoThreeSpectrum1937.graph
    sourceMap1381swap fusedMap1381swap sourceMap1381swap_checked fusedMap1381swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1381
#print axioms sourceMap1381swap_checked
#print axioms fusedMap1381swap_checked
#print axioms certified1381swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
