/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1370 : Family 9 := level9.get ⟨521,by decide⟩
def sourceMap1370 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,4,5,6,7,8,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1370 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1370_checked : acceptsGraphIso
    (source (graph core1370) (root 9) 0 2) DegreeTwoThreeSpectrum2192.graph sourceMap1370=true := by decide +kernel
theorem fusedMap1370_checked : acceptsGraphIso
    (fused (graph core1370) (root 9) 0 2) DegreeTwoThreeSpectrum2233.graph fusedMap1370=true := by decide +kernel
theorem certified1370 : Certified (graph core1370) (root 9) 0 2 :=
  of_native_maps core1370 DegreeTwoThreeSpectrum2192.graph DegreeTwoThreeSpectrum2233.graph
    sourceMap1370 fusedMap1370 sourceMap1370_checked fusedMap1370_checked
    DegreeTwoThreeFiniteComparisons.comparison1370
#print axioms sourceMap1370_checked
#print axioms fusedMap1370_checked
#print axioms certified1370
def sourceMap1370swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,4,5,6,7,1,2,3,8] (sourceLabel 9 2 0 v)
def fusedMap1370swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1370swap_checked : acceptsGraphIso
    (source (graph core1370) (root 9) 2 0) DegreeTwoThreeSpectrum2192.graph sourceMap1370swap=true := by decide +kernel
theorem fusedMap1370swap_checked : acceptsGraphIso
    (fused (graph core1370) (root 9) 2 0) DegreeTwoThreeSpectrum2233.graph fusedMap1370swap=true := by decide +kernel
theorem certified1370swap : Certified (graph core1370) (root 9) 2 0 :=
  of_native_maps core1370 DegreeTwoThreeSpectrum2192.graph DegreeTwoThreeSpectrum2233.graph
    sourceMap1370swap fusedMap1370swap sourceMap1370swap_checked fusedMap1370swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1370
#print axioms sourceMap1370swap_checked
#print axioms fusedMap1370swap_checked
#print axioms certified1370swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
