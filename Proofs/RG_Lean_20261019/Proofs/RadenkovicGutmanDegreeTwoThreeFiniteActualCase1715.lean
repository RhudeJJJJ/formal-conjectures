/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1715 : Family 10 := level10.get ⟨917,by decide⟩
def sourceMap1715 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1715 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1715_checked : acceptsGraphIso
    (source (graph core1715) (root 10) 0 2) DegreeTwoThreeSpectrum3297.graph sourceMap1715=true := by decide +kernel
theorem fusedMap1715_checked : acceptsGraphIso
    (fused (graph core1715) (root 10) 0 2) DegreeTwoThreeSpectrum2931.graph fusedMap1715=true := by decide +kernel
theorem certified1715 : Certified (graph core1715) (root 10) 0 2 :=
  of_native_maps core1715 DegreeTwoThreeSpectrum3297.graph DegreeTwoThreeSpectrum2931.graph
    sourceMap1715 fusedMap1715 sourceMap1715_checked fusedMap1715_checked
    DegreeTwoThreeFiniteComparisons.comparison1715
#print axioms sourceMap1715_checked
#print axioms fusedMap1715_checked
#print axioms certified1715
def sourceMap1715swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1715swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1715swap_checked : acceptsGraphIso
    (source (graph core1715) (root 10) 2 0) DegreeTwoThreeSpectrum3297.graph sourceMap1715swap=true := by decide +kernel
theorem fusedMap1715swap_checked : acceptsGraphIso
    (fused (graph core1715) (root 10) 2 0) DegreeTwoThreeSpectrum2931.graph fusedMap1715swap=true := by decide +kernel
theorem certified1715swap : Certified (graph core1715) (root 10) 2 0 :=
  of_native_maps core1715 DegreeTwoThreeSpectrum3297.graph DegreeTwoThreeSpectrum2931.graph
    sourceMap1715swap fusedMap1715swap sourceMap1715swap_checked fusedMap1715swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1715
#print axioms sourceMap1715swap_checked
#print axioms fusedMap1715swap_checked
#print axioms certified1715swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
