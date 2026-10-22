/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1359 : Family 9 := level9.get ⟨502,by decide⟩
def sourceMap1359 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1359 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1359_checked : acceptsGraphIso
    (source (graph core1359) (root 9) 0 2) DegreeTwoThreeSpectrum2206.graph sourceMap1359=true := by decide +kernel
theorem fusedMap1359_checked : acceptsGraphIso
    (fused (graph core1359) (root 9) 0 2) DegreeTwoThreeSpectrum2207.graph fusedMap1359=true := by decide +kernel
theorem certified1359 : Certified (graph core1359) (root 9) 0 2 :=
  of_native_maps core1359 DegreeTwoThreeSpectrum2206.graph DegreeTwoThreeSpectrum2207.graph
    sourceMap1359 fusedMap1359 sourceMap1359_checked fusedMap1359_checked
    DegreeTwoThreeFiniteComparisons.comparison1359
#print axioms sourceMap1359_checked
#print axioms fusedMap1359_checked
#print axioms certified1359
def sourceMap1359swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1359swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1359swap_checked : acceptsGraphIso
    (source (graph core1359) (root 9) 2 0) DegreeTwoThreeSpectrum2206.graph sourceMap1359swap=true := by decide +kernel
theorem fusedMap1359swap_checked : acceptsGraphIso
    (fused (graph core1359) (root 9) 2 0) DegreeTwoThreeSpectrum2207.graph fusedMap1359swap=true := by decide +kernel
theorem certified1359swap : Certified (graph core1359) (root 9) 2 0 :=
  of_native_maps core1359 DegreeTwoThreeSpectrum2206.graph DegreeTwoThreeSpectrum2207.graph
    sourceMap1359swap fusedMap1359swap sourceMap1359swap_checked fusedMap1359swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1359
#print axioms sourceMap1359swap_checked
#print axioms fusedMap1359swap_checked
#print axioms certified1359swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
