/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1375 : Family 9 := level9.get ⟨535,by decide⟩
def sourceMap1375 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,4,5,6,7,8,9,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1375 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1375_checked : acceptsGraphIso
    (source (graph core1375) (root 9) 0 2) DegreeTwoThreeSpectrum2191.graph sourceMap1375=true := by decide +kernel
theorem fusedMap1375_checked : acceptsGraphIso
    (fused (graph core1375) (root 9) 0 2) DegreeTwoThreeSpectrum2238.graph fusedMap1375=true := by decide +kernel
theorem certified1375 : Certified (graph core1375) (root 9) 0 2 :=
  of_native_maps core1375 DegreeTwoThreeSpectrum2191.graph DegreeTwoThreeSpectrum2238.graph
    sourceMap1375 fusedMap1375 sourceMap1375_checked fusedMap1375_checked
    DegreeTwoThreeFiniteComparisons.comparison1375
#print axioms sourceMap1375_checked
#print axioms fusedMap1375_checked
#print axioms certified1375
def sourceMap1375swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,10,11,12,13,4,5,6,7,8,1,2,3,9] (sourceLabel 9 2 0 v)
def fusedMap1375swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1375swap_checked : acceptsGraphIso
    (source (graph core1375) (root 9) 2 0) DegreeTwoThreeSpectrum2191.graph sourceMap1375swap=true := by decide +kernel
theorem fusedMap1375swap_checked : acceptsGraphIso
    (fused (graph core1375) (root 9) 2 0) DegreeTwoThreeSpectrum2238.graph fusedMap1375swap=true := by decide +kernel
theorem certified1375swap : Certified (graph core1375) (root 9) 2 0 :=
  of_native_maps core1375 DegreeTwoThreeSpectrum2191.graph DegreeTwoThreeSpectrum2238.graph
    sourceMap1375swap fusedMap1375swap sourceMap1375swap_checked fusedMap1375swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1375
#print axioms sourceMap1375swap_checked
#print axioms fusedMap1375swap_checked
#print axioms certified1375swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
