/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1758 : Family 10 := level10.get ⟨1026,by decide⟩
def sourceMap1758 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1758 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1758_checked : acceptsGraphIso
    (source (graph core1758) (root 10) 0 2) DegreeTwoThreeSpectrum3050.graph sourceMap1758=true := by decide +kernel
theorem fusedMap1758_checked : acceptsGraphIso
    (fused (graph core1758) (root 10) 0 2) DegreeTwoThreeSpectrum3052.graph fusedMap1758=true := by decide +kernel
theorem certified1758 : Certified (graph core1758) (root 10) 0 2 :=
  of_native_maps core1758 DegreeTwoThreeSpectrum3050.graph DegreeTwoThreeSpectrum3052.graph
    sourceMap1758 fusedMap1758 sourceMap1758_checked fusedMap1758_checked
    DegreeTwoThreeFiniteComparisons.comparison1758
#print axioms sourceMap1758_checked
#print axioms fusedMap1758_checked
#print axioms certified1758
def sourceMap1758swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1758swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1758swap_checked : acceptsGraphIso
    (source (graph core1758) (root 10) 2 0) DegreeTwoThreeSpectrum3050.graph sourceMap1758swap=true := by decide +kernel
theorem fusedMap1758swap_checked : acceptsGraphIso
    (fused (graph core1758) (root 10) 2 0) DegreeTwoThreeSpectrum3052.graph fusedMap1758swap=true := by decide +kernel
theorem certified1758swap : Certified (graph core1758) (root 10) 2 0 :=
  of_native_maps core1758 DegreeTwoThreeSpectrum3050.graph DegreeTwoThreeSpectrum3052.graph
    sourceMap1758swap fusedMap1758swap sourceMap1758swap_checked fusedMap1758swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1758
#print axioms sourceMap1758swap_checked
#print axioms fusedMap1758swap_checked
#print axioms certified1758swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
