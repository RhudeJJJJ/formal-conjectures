/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1699 : Family 10 := level10.get ⟨880,by decide⟩
def sourceMap1699 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1699 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1699_checked : acceptsGraphIso
    (source (graph core1699) (root 10) 0 2) DegreeTwoThreeSpectrum3698.graph sourceMap1699=true := by decide +kernel
theorem fusedMap1699_checked : acceptsGraphIso
    (fused (graph core1699) (root 10) 0 2) DegreeTwoThreeSpectrum2874.graph fusedMap1699=true := by decide +kernel
theorem certified1699 : Certified (graph core1699) (root 10) 0 2 :=
  of_native_maps core1699 DegreeTwoThreeSpectrum3698.graph DegreeTwoThreeSpectrum2874.graph
    sourceMap1699 fusedMap1699 sourceMap1699_checked fusedMap1699_checked
    DegreeTwoThreeFiniteComparisons.comparison1699
#print axioms sourceMap1699_checked
#print axioms fusedMap1699_checked
#print axioms certified1699
def sourceMap1699swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1699swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1699swap_checked : acceptsGraphIso
    (source (graph core1699) (root 10) 2 0) DegreeTwoThreeSpectrum3698.graph sourceMap1699swap=true := by decide +kernel
theorem fusedMap1699swap_checked : acceptsGraphIso
    (fused (graph core1699) (root 10) 2 0) DegreeTwoThreeSpectrum2874.graph fusedMap1699swap=true := by decide +kernel
theorem certified1699swap : Certified (graph core1699) (root 10) 2 0 :=
  of_native_maps core1699 DegreeTwoThreeSpectrum3698.graph DegreeTwoThreeSpectrum2874.graph
    sourceMap1699swap fusedMap1699swap sourceMap1699swap_checked fusedMap1699swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1699
#print axioms sourceMap1699swap_checked
#print axioms fusedMap1699swap_checked
#print axioms certified1699swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
