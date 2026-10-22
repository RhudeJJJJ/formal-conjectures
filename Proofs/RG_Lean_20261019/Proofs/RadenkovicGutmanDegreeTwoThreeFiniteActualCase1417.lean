/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1417 : Family 9 := level9.get ⟨642,by decide⟩
def sourceMap1417 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1417 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1417_checked : acceptsGraphIso
    (source (graph core1417) (root 9) 0 2) DegreeTwoThreeSpectrum2292.graph sourceMap1417=true := by decide +kernel
theorem fusedMap1417_checked : acceptsGraphIso
    (fused (graph core1417) (root 9) 0 2) DegreeTwoThreeSpectrum2095.graph fusedMap1417=true := by decide +kernel
theorem certified1417 : Certified (graph core1417) (root 9) 0 2 :=
  of_native_maps core1417 DegreeTwoThreeSpectrum2292.graph DegreeTwoThreeSpectrum2095.graph
    sourceMap1417 fusedMap1417 sourceMap1417_checked fusedMap1417_checked
    DegreeTwoThreeFiniteComparisons.comparison1417
#print axioms sourceMap1417_checked
#print axioms fusedMap1417_checked
#print axioms certified1417
def sourceMap1417swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1417swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1417swap_checked : acceptsGraphIso
    (source (graph core1417) (root 9) 2 0) DegreeTwoThreeSpectrum2292.graph sourceMap1417swap=true := by decide +kernel
theorem fusedMap1417swap_checked : acceptsGraphIso
    (fused (graph core1417) (root 9) 2 0) DegreeTwoThreeSpectrum2095.graph fusedMap1417swap=true := by decide +kernel
theorem certified1417swap : Certified (graph core1417) (root 9) 2 0 :=
  of_native_maps core1417 DegreeTwoThreeSpectrum2292.graph DegreeTwoThreeSpectrum2095.graph
    sourceMap1417swap fusedMap1417swap sourceMap1417swap_checked fusedMap1417swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1417
#print axioms sourceMap1417swap_checked
#print axioms fusedMap1417swap_checked
#print axioms certified1417swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
