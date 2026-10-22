/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1399 : Family 9 := level9.get ⟨596,by decide⟩
def sourceMap1399 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1399 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1399_checked : acceptsGraphIso
    (source (graph core1399) (root 9) 0 2) DegreeTwoThreeSpectrum2271.graph sourceMap1399=true := by decide +kernel
theorem fusedMap1399_checked : acceptsGraphIso
    (fused (graph core1399) (root 9) 0 2) DegreeTwoThreeSpectrum1999.graph fusedMap1399=true := by decide +kernel
theorem certified1399 : Certified (graph core1399) (root 9) 0 2 :=
  of_native_maps core1399 DegreeTwoThreeSpectrum2271.graph DegreeTwoThreeSpectrum1999.graph
    sourceMap1399 fusedMap1399 sourceMap1399_checked fusedMap1399_checked
    DegreeTwoThreeFiniteComparisons.comparison1399
#print axioms sourceMap1399_checked
#print axioms fusedMap1399_checked
#print axioms certified1399
def sourceMap1399swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1399swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1399swap_checked : acceptsGraphIso
    (source (graph core1399) (root 9) 2 0) DegreeTwoThreeSpectrum2271.graph sourceMap1399swap=true := by decide +kernel
theorem fusedMap1399swap_checked : acceptsGraphIso
    (fused (graph core1399) (root 9) 2 0) DegreeTwoThreeSpectrum1999.graph fusedMap1399swap=true := by decide +kernel
theorem certified1399swap : Certified (graph core1399) (root 9) 2 0 :=
  of_native_maps core1399 DegreeTwoThreeSpectrum2271.graph DegreeTwoThreeSpectrum1999.graph
    sourceMap1399swap fusedMap1399swap sourceMap1399swap_checked fusedMap1399swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1399
#print axioms sourceMap1399swap_checked
#print axioms fusedMap1399swap_checked
#print axioms certified1399swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
