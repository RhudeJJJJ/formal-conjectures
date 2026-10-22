/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1383 : Family 9 := level9.get ⟨558,by decide⟩
def sourceMap1383 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1383 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1383_checked : acceptsGraphIso
    (source (graph core1383) (root 9) 0 2) DegreeTwoThreeSpectrum2254.graph sourceMap1383=true := by decide +kernel
theorem fusedMap1383_checked : acceptsGraphIso
    (fused (graph core1383) (root 9) 0 2) DegreeTwoThreeSpectrum1941.graph fusedMap1383=true := by decide +kernel
theorem certified1383 : Certified (graph core1383) (root 9) 0 2 :=
  of_native_maps core1383 DegreeTwoThreeSpectrum2254.graph DegreeTwoThreeSpectrum1941.graph
    sourceMap1383 fusedMap1383 sourceMap1383_checked fusedMap1383_checked
    DegreeTwoThreeFiniteComparisons.comparison1383
#print axioms sourceMap1383_checked
#print axioms fusedMap1383_checked
#print axioms certified1383
def sourceMap1383swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1383swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1383swap_checked : acceptsGraphIso
    (source (graph core1383) (root 9) 2 0) DegreeTwoThreeSpectrum2254.graph sourceMap1383swap=true := by decide +kernel
theorem fusedMap1383swap_checked : acceptsGraphIso
    (fused (graph core1383) (root 9) 2 0) DegreeTwoThreeSpectrum1941.graph fusedMap1383swap=true := by decide +kernel
theorem certified1383swap : Certified (graph core1383) (root 9) 2 0 :=
  of_native_maps core1383 DegreeTwoThreeSpectrum2254.graph DegreeTwoThreeSpectrum1941.graph
    sourceMap1383swap fusedMap1383swap sourceMap1383swap_checked fusedMap1383swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1383
#print axioms sourceMap1383swap_checked
#print axioms fusedMap1383swap_checked
#print axioms certified1383swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
