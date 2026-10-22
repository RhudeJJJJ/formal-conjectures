/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1395 : Family 9 := level9.get ⟨588,by decide⟩
def sourceMap1395 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1395 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1395_checked : acceptsGraphIso
    (source (graph core1395) (root 9) 0 2) DegreeTwoThreeSpectrum2267.graph sourceMap1395=true := by decide +kernel
theorem fusedMap1395_checked : acceptsGraphIso
    (fused (graph core1395) (root 9) 0 2) DegreeTwoThreeSpectrum1990.graph fusedMap1395=true := by decide +kernel
theorem certified1395 : Certified (graph core1395) (root 9) 0 2 :=
  of_native_maps core1395 DegreeTwoThreeSpectrum2267.graph DegreeTwoThreeSpectrum1990.graph
    sourceMap1395 fusedMap1395 sourceMap1395_checked fusedMap1395_checked
    DegreeTwoThreeFiniteComparisons.comparison1395
#print axioms sourceMap1395_checked
#print axioms fusedMap1395_checked
#print axioms certified1395
def sourceMap1395swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1395swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1395swap_checked : acceptsGraphIso
    (source (graph core1395) (root 9) 2 0) DegreeTwoThreeSpectrum2267.graph sourceMap1395swap=true := by decide +kernel
theorem fusedMap1395swap_checked : acceptsGraphIso
    (fused (graph core1395) (root 9) 2 0) DegreeTwoThreeSpectrum1990.graph fusedMap1395swap=true := by decide +kernel
theorem certified1395swap : Certified (graph core1395) (root 9) 2 0 :=
  of_native_maps core1395 DegreeTwoThreeSpectrum2267.graph DegreeTwoThreeSpectrum1990.graph
    sourceMap1395swap fusedMap1395swap sourceMap1395swap_checked fusedMap1395swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1395
#print axioms sourceMap1395swap_checked
#print axioms fusedMap1395swap_checked
#print axioms certified1395swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
