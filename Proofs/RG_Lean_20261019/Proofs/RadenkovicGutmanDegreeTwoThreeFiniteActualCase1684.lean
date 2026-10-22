/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1684 : Family 10 := level10.get ⟨837,by decide⟩
def sourceMap1684 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1684 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1684_checked : acceptsGraphIso
    (source (graph core1684) (root 10) 0 2) DegreeTwoThreeSpectrum3631.graph sourceMap1684=true := by decide +kernel
theorem fusedMap1684_checked : acceptsGraphIso
    (fused (graph core1684) (root 10) 0 2) DegreeTwoThreeSpectrum2824.graph fusedMap1684=true := by decide +kernel
theorem certified1684 : Certified (graph core1684) (root 10) 0 2 :=
  of_native_maps core1684 DegreeTwoThreeSpectrum3631.graph DegreeTwoThreeSpectrum2824.graph
    sourceMap1684 fusedMap1684 sourceMap1684_checked fusedMap1684_checked
    DegreeTwoThreeFiniteComparisons.comparison1684
#print axioms sourceMap1684_checked
#print axioms fusedMap1684_checked
#print axioms certified1684
def sourceMap1684swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1684swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1684swap_checked : acceptsGraphIso
    (source (graph core1684) (root 10) 2 0) DegreeTwoThreeSpectrum3631.graph sourceMap1684swap=true := by decide +kernel
theorem fusedMap1684swap_checked : acceptsGraphIso
    (fused (graph core1684) (root 10) 2 0) DegreeTwoThreeSpectrum2824.graph fusedMap1684swap=true := by decide +kernel
theorem certified1684swap : Certified (graph core1684) (root 10) 2 0 :=
  of_native_maps core1684 DegreeTwoThreeSpectrum3631.graph DegreeTwoThreeSpectrum2824.graph
    sourceMap1684swap fusedMap1684swap sourceMap1684swap_checked fusedMap1684swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1684
#print axioms sourceMap1684swap_checked
#print axioms fusedMap1684swap_checked
#print axioms certified1684swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
