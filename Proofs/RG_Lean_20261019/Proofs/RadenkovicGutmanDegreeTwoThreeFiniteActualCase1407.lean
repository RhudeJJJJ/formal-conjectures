/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1407 : Family 9 := level9.get ⟨611,by decide⟩
def sourceMap1407 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1407 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1407_checked : acceptsGraphIso
    (source (graph core1407) (root 9) 0 2) DegreeTwoThreeSpectrum2280.graph sourceMap1407=true := by decide +kernel
theorem fusedMap1407_checked : acceptsGraphIso
    (fused (graph core1407) (root 9) 0 2) DegreeTwoThreeSpectrum2022.graph fusedMap1407=true := by decide +kernel
theorem certified1407 : Certified (graph core1407) (root 9) 0 2 :=
  of_native_maps core1407 DegreeTwoThreeSpectrum2280.graph DegreeTwoThreeSpectrum2022.graph
    sourceMap1407 fusedMap1407 sourceMap1407_checked fusedMap1407_checked
    DegreeTwoThreeFiniteComparisons.comparison1407
#print axioms sourceMap1407_checked
#print axioms fusedMap1407_checked
#print axioms certified1407
def sourceMap1407swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1407swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1407swap_checked : acceptsGraphIso
    (source (graph core1407) (root 9) 2 0) DegreeTwoThreeSpectrum2280.graph sourceMap1407swap=true := by decide +kernel
theorem fusedMap1407swap_checked : acceptsGraphIso
    (fused (graph core1407) (root 9) 2 0) DegreeTwoThreeSpectrum2022.graph fusedMap1407swap=true := by decide +kernel
theorem certified1407swap : Certified (graph core1407) (root 9) 2 0 :=
  of_native_maps core1407 DegreeTwoThreeSpectrum2280.graph DegreeTwoThreeSpectrum2022.graph
    sourceMap1407swap fusedMap1407swap sourceMap1407swap_checked fusedMap1407swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1407
#print axioms sourceMap1407swap_checked
#print axioms fusedMap1407swap_checked
#print axioms certified1407swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
