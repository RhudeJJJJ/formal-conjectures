/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1388 : Family 9 := level9.get ⟨571,by decide⟩
def sourceMap1388 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1388 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1388_checked : acceptsGraphIso
    (source (graph core1388) (root 9) 0 2) DegreeTwoThreeSpectrum2259.graph sourceMap1388=true := by decide +kernel
theorem fusedMap1388_checked : acceptsGraphIso
    (fused (graph core1388) (root 9) 0 2) DegreeTwoThreeSpectrum1958.graph fusedMap1388=true := by decide +kernel
theorem certified1388 : Certified (graph core1388) (root 9) 0 2 :=
  of_native_maps core1388 DegreeTwoThreeSpectrum2259.graph DegreeTwoThreeSpectrum1958.graph
    sourceMap1388 fusedMap1388 sourceMap1388_checked fusedMap1388_checked
    DegreeTwoThreeFiniteComparisons.comparison1388
#print axioms sourceMap1388_checked
#print axioms fusedMap1388_checked
#print axioms certified1388
def sourceMap1388swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1388swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1388swap_checked : acceptsGraphIso
    (source (graph core1388) (root 9) 2 0) DegreeTwoThreeSpectrum2259.graph sourceMap1388swap=true := by decide +kernel
theorem fusedMap1388swap_checked : acceptsGraphIso
    (fused (graph core1388) (root 9) 2 0) DegreeTwoThreeSpectrum1958.graph fusedMap1388swap=true := by decide +kernel
theorem certified1388swap : Certified (graph core1388) (root 9) 2 0 :=
  of_native_maps core1388 DegreeTwoThreeSpectrum2259.graph DegreeTwoThreeSpectrum1958.graph
    sourceMap1388swap fusedMap1388swap sourceMap1388swap_checked fusedMap1388swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1388
#print axioms sourceMap1388swap_checked
#print axioms fusedMap1388swap_checked
#print axioms certified1388swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
