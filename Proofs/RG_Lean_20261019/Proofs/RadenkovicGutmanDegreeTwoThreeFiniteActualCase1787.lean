/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1787 : Family 10 := level10.get ⟨1101,by decide⟩
def sourceMap1787 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1787 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1787_checked : acceptsGraphIso
    (source (graph core1787) (root 10) 0 2) DegreeTwoThreeSpectrum3168.graph sourceMap1787=true := by decide +kernel
theorem fusedMap1787_checked : acceptsGraphIso
    (fused (graph core1787) (root 10) 0 2) DegreeTwoThreeSpectrum3170.graph fusedMap1787=true := by decide +kernel
theorem certified1787 : Certified (graph core1787) (root 10) 0 2 :=
  of_native_maps core1787 DegreeTwoThreeSpectrum3168.graph DegreeTwoThreeSpectrum3170.graph
    sourceMap1787 fusedMap1787 sourceMap1787_checked fusedMap1787_checked
    DegreeTwoThreeFiniteComparisons.comparison1787
#print axioms sourceMap1787_checked
#print axioms fusedMap1787_checked
#print axioms certified1787
def sourceMap1787swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1787swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1787swap_checked : acceptsGraphIso
    (source (graph core1787) (root 10) 2 0) DegreeTwoThreeSpectrum3168.graph sourceMap1787swap=true := by decide +kernel
theorem fusedMap1787swap_checked : acceptsGraphIso
    (fused (graph core1787) (root 10) 2 0) DegreeTwoThreeSpectrum3170.graph fusedMap1787swap=true := by decide +kernel
theorem certified1787swap : Certified (graph core1787) (root 10) 2 0 :=
  of_native_maps core1787 DegreeTwoThreeSpectrum3168.graph DegreeTwoThreeSpectrum3170.graph
    sourceMap1787swap fusedMap1787swap sourceMap1787swap_checked fusedMap1787swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1787
#print axioms sourceMap1787swap_checked
#print axioms fusedMap1787swap_checked
#print axioms certified1787swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
