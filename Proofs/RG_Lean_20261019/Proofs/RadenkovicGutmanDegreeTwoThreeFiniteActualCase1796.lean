/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1796 : Family 10 := level10.get ⟨1123,by decide⟩
def sourceMap1796 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1796 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1796_checked : acceptsGraphIso
    (source (graph core1796) (root 10) 0 2) DegreeTwoThreeSpectrum3200.graph sourceMap1796=true := by decide +kernel
theorem fusedMap1796_checked : acceptsGraphIso
    (fused (graph core1796) (root 10) 0 2) DegreeTwoThreeSpectrum3204.graph fusedMap1796=true := by decide +kernel
theorem certified1796 : Certified (graph core1796) (root 10) 0 2 :=
  of_native_maps core1796 DegreeTwoThreeSpectrum3200.graph DegreeTwoThreeSpectrum3204.graph
    sourceMap1796 fusedMap1796 sourceMap1796_checked fusedMap1796_checked
    DegreeTwoThreeFiniteComparisons.comparison1796
#print axioms sourceMap1796_checked
#print axioms fusedMap1796_checked
#print axioms certified1796
def sourceMap1796swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1796swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1796swap_checked : acceptsGraphIso
    (source (graph core1796) (root 10) 2 0) DegreeTwoThreeSpectrum3200.graph sourceMap1796swap=true := by decide +kernel
theorem fusedMap1796swap_checked : acceptsGraphIso
    (fused (graph core1796) (root 10) 2 0) DegreeTwoThreeSpectrum3204.graph fusedMap1796swap=true := by decide +kernel
theorem certified1796swap : Certified (graph core1796) (root 10) 2 0 :=
  of_native_maps core1796 DegreeTwoThreeSpectrum3200.graph DegreeTwoThreeSpectrum3204.graph
    sourceMap1796swap fusedMap1796swap sourceMap1796swap_checked fusedMap1796swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1796
#print axioms sourceMap1796swap_checked
#print axioms fusedMap1796swap_checked
#print axioms certified1796swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
