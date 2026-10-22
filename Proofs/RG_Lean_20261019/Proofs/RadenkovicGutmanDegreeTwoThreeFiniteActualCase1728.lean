/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1728 : Family 10 := level10.get ⟨952,by decide⟩
def sourceMap1728 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1728 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1728_checked : acceptsGraphIso
    (source (graph core1728) (root 10) 0 2) DegreeTwoThreeSpectrum3685.graph sourceMap1728=true := by decide +kernel
theorem fusedMap1728_checked : acceptsGraphIso
    (fused (graph core1728) (root 10) 0 2) DegreeTwoThreeSpectrum2975.graph fusedMap1728=true := by decide +kernel
theorem certified1728 : Certified (graph core1728) (root 10) 0 2 :=
  of_native_maps core1728 DegreeTwoThreeSpectrum3685.graph DegreeTwoThreeSpectrum2975.graph
    sourceMap1728 fusedMap1728 sourceMap1728_checked fusedMap1728_checked
    DegreeTwoThreeFiniteComparisons.comparison1728
#print axioms sourceMap1728_checked
#print axioms fusedMap1728_checked
#print axioms certified1728
def sourceMap1728swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1728swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1728swap_checked : acceptsGraphIso
    (source (graph core1728) (root 10) 2 0) DegreeTwoThreeSpectrum3685.graph sourceMap1728swap=true := by decide +kernel
theorem fusedMap1728swap_checked : acceptsGraphIso
    (fused (graph core1728) (root 10) 2 0) DegreeTwoThreeSpectrum2975.graph fusedMap1728swap=true := by decide +kernel
theorem certified1728swap : Certified (graph core1728) (root 10) 2 0 :=
  of_native_maps core1728 DegreeTwoThreeSpectrum3685.graph DegreeTwoThreeSpectrum2975.graph
    sourceMap1728swap fusedMap1728swap sourceMap1728swap_checked fusedMap1728swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1728
#print axioms sourceMap1728swap_checked
#print axioms fusedMap1728swap_checked
#print axioms certified1728swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
