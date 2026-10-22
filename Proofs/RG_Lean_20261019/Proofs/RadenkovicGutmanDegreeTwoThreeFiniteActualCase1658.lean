/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1658 : Family 10 := level10.get ⟨770,by decide⟩
def sourceMap1658 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1658 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1658_checked : acceptsGraphIso
    (source (graph core1658) (root 10) 0 2) DegreeTwoThreeSpectrum3550.graph sourceMap1658=true := by decide +kernel
theorem fusedMap1658_checked : acceptsGraphIso
    (fused (graph core1658) (root 10) 0 2) DegreeTwoThreeSpectrum2737.graph fusedMap1658=true := by decide +kernel
theorem certified1658 : Certified (graph core1658) (root 10) 0 2 :=
  of_native_maps core1658 DegreeTwoThreeSpectrum3550.graph DegreeTwoThreeSpectrum2737.graph
    sourceMap1658 fusedMap1658 sourceMap1658_checked fusedMap1658_checked
    DegreeTwoThreeFiniteComparisons.comparison1658
#print axioms sourceMap1658_checked
#print axioms fusedMap1658_checked
#print axioms certified1658
def sourceMap1658swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1658swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1658swap_checked : acceptsGraphIso
    (source (graph core1658) (root 10) 2 0) DegreeTwoThreeSpectrum3550.graph sourceMap1658swap=true := by decide +kernel
theorem fusedMap1658swap_checked : acceptsGraphIso
    (fused (graph core1658) (root 10) 2 0) DegreeTwoThreeSpectrum2737.graph fusedMap1658swap=true := by decide +kernel
theorem certified1658swap : Certified (graph core1658) (root 10) 2 0 :=
  of_native_maps core1658 DegreeTwoThreeSpectrum3550.graph DegreeTwoThreeSpectrum2737.graph
    sourceMap1658swap fusedMap1658swap sourceMap1658swap_checked fusedMap1658swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1658
#print axioms sourceMap1658swap_checked
#print axioms fusedMap1658swap_checked
#print axioms certified1658swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
