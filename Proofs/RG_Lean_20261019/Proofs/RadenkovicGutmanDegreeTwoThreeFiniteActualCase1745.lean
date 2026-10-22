/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1745 : Family 10 := level10.get ⟨983,by decide⟩
def sourceMap1745 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1745 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1745_checked : acceptsGraphIso
    (source (graph core1745) (root 10) 0 2) DegreeTwoThreeSpectrum3422.graph sourceMap1745=true := by decide +kernel
theorem fusedMap1745_checked : acceptsGraphIso
    (fused (graph core1745) (root 10) 0 2) DegreeTwoThreeSpectrum2949.graph fusedMap1745=true := by decide +kernel
theorem certified1745 : Certified (graph core1745) (root 10) 0 2 :=
  of_native_maps core1745 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2949.graph
    sourceMap1745 fusedMap1745 sourceMap1745_checked fusedMap1745_checked
    DegreeTwoThreeFiniteComparisons.comparison1745
#print axioms sourceMap1745_checked
#print axioms fusedMap1745_checked
#print axioms certified1745
def sourceMap1745swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1745swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1745swap_checked : acceptsGraphIso
    (source (graph core1745) (root 10) 2 0) DegreeTwoThreeSpectrum3422.graph sourceMap1745swap=true := by decide +kernel
theorem fusedMap1745swap_checked : acceptsGraphIso
    (fused (graph core1745) (root 10) 2 0) DegreeTwoThreeSpectrum2949.graph fusedMap1745swap=true := by decide +kernel
theorem certified1745swap : Certified (graph core1745) (root 10) 2 0 :=
  of_native_maps core1745 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2949.graph
    sourceMap1745swap fusedMap1745swap sourceMap1745swap_checked fusedMap1745swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1745
#print axioms sourceMap1745swap_checked
#print axioms fusedMap1745swap_checked
#print axioms certified1745swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
