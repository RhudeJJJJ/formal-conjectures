/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1824 : Family 10 := level10.get ⟨1195,by decide⟩
def sourceMap1824 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1824 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1824_checked : acceptsGraphIso
    (source (graph core1824) (root 10) 0 2) DegreeTwoThreeSpectrum3312.graph sourceMap1824=true := by decide +kernel
theorem fusedMap1824_checked : acceptsGraphIso
    (fused (graph core1824) (root 10) 0 2) DegreeTwoThreeSpectrum3313.graph fusedMap1824=true := by decide +kernel
theorem certified1824 : Certified (graph core1824) (root 10) 0 2 :=
  of_native_maps core1824 DegreeTwoThreeSpectrum3312.graph DegreeTwoThreeSpectrum3313.graph
    sourceMap1824 fusedMap1824 sourceMap1824_checked fusedMap1824_checked
    DegreeTwoThreeFiniteComparisons.comparison1824
#print axioms sourceMap1824_checked
#print axioms fusedMap1824_checked
#print axioms certified1824
def sourceMap1824swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1824swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1824swap_checked : acceptsGraphIso
    (source (graph core1824) (root 10) 2 0) DegreeTwoThreeSpectrum3312.graph sourceMap1824swap=true := by decide +kernel
theorem fusedMap1824swap_checked : acceptsGraphIso
    (fused (graph core1824) (root 10) 2 0) DegreeTwoThreeSpectrum3313.graph fusedMap1824swap=true := by decide +kernel
theorem certified1824swap : Certified (graph core1824) (root 10) 2 0 :=
  of_native_maps core1824 DegreeTwoThreeSpectrum3312.graph DegreeTwoThreeSpectrum3313.graph
    sourceMap1824swap fusedMap1824swap sourceMap1824swap_checked fusedMap1824swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1824
#print axioms sourceMap1824swap_checked
#print axioms fusedMap1824swap_checked
#print axioms certified1824swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
