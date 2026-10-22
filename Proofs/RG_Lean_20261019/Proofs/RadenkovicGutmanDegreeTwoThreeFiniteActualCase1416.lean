/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1416 : Family 9 := level9.get ⟨639,by decide⟩
def sourceMap1416 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1416 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1416_checked : acceptsGraphIso
    (source (graph core1416) (root 9) 0 2) DegreeTwoThreeSpectrum2291.graph sourceMap1416=true := by decide +kernel
theorem fusedMap1416_checked : acceptsGraphIso
    (fused (graph core1416) (root 9) 0 2) DegreeTwoThreeSpectrum2088.graph fusedMap1416=true := by decide +kernel
theorem certified1416 : Certified (graph core1416) (root 9) 0 2 :=
  of_native_maps core1416 DegreeTwoThreeSpectrum2291.graph DegreeTwoThreeSpectrum2088.graph
    sourceMap1416 fusedMap1416 sourceMap1416_checked fusedMap1416_checked
    DegreeTwoThreeFiniteComparisons.comparison1416
#print axioms sourceMap1416_checked
#print axioms fusedMap1416_checked
#print axioms certified1416
def sourceMap1416swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1416swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1416swap_checked : acceptsGraphIso
    (source (graph core1416) (root 9) 2 0) DegreeTwoThreeSpectrum2291.graph sourceMap1416swap=true := by decide +kernel
theorem fusedMap1416swap_checked : acceptsGraphIso
    (fused (graph core1416) (root 9) 2 0) DegreeTwoThreeSpectrum2088.graph fusedMap1416swap=true := by decide +kernel
theorem certified1416swap : Certified (graph core1416) (root 9) 2 0 :=
  of_native_maps core1416 DegreeTwoThreeSpectrum2291.graph DegreeTwoThreeSpectrum2088.graph
    sourceMap1416swap fusedMap1416swap sourceMap1416swap_checked fusedMap1416swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1416
#print axioms sourceMap1416swap_checked
#print axioms fusedMap1416swap_checked
#print axioms certified1416swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
