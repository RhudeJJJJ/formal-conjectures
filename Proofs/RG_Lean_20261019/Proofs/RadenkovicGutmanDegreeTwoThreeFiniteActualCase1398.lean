/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1398 : Family 9 := level9.get ⟨594,by decide⟩
def sourceMap1398 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1398 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1398_checked : acceptsGraphIso
    (source (graph core1398) (root 9) 0 2) DegreeTwoThreeSpectrum2270.graph sourceMap1398=true := by decide +kernel
theorem fusedMap1398_checked : acceptsGraphIso
    (fused (graph core1398) (root 9) 0 2) DegreeTwoThreeSpectrum1996.graph fusedMap1398=true := by decide +kernel
theorem certified1398 : Certified (graph core1398) (root 9) 0 2 :=
  of_native_maps core1398 DegreeTwoThreeSpectrum2270.graph DegreeTwoThreeSpectrum1996.graph
    sourceMap1398 fusedMap1398 sourceMap1398_checked fusedMap1398_checked
    DegreeTwoThreeFiniteComparisons.comparison1398
#print axioms sourceMap1398_checked
#print axioms fusedMap1398_checked
#print axioms certified1398
def sourceMap1398swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1398swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1398swap_checked : acceptsGraphIso
    (source (graph core1398) (root 9) 2 0) DegreeTwoThreeSpectrum2270.graph sourceMap1398swap=true := by decide +kernel
theorem fusedMap1398swap_checked : acceptsGraphIso
    (fused (graph core1398) (root 9) 2 0) DegreeTwoThreeSpectrum1996.graph fusedMap1398swap=true := by decide +kernel
theorem certified1398swap : Certified (graph core1398) (root 9) 2 0 :=
  of_native_maps core1398 DegreeTwoThreeSpectrum2270.graph DegreeTwoThreeSpectrum1996.graph
    sourceMap1398swap fusedMap1398swap sourceMap1398swap_checked fusedMap1398swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1398
#print axioms sourceMap1398swap_checked
#print axioms fusedMap1398swap_checked
#print axioms certified1398swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
