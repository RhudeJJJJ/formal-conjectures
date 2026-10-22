/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1702 : Family 10 := level10.get ⟨888,by decide⟩
def sourceMap1702 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1702 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1702_checked : acceptsGraphIso
    (source (graph core1702) (root 10) 0 2) DegreeTwoThreeSpectrum3702.graph sourceMap1702=true := by decide +kernel
theorem fusedMap1702_checked : acceptsGraphIso
    (fused (graph core1702) (root 10) 0 2) DegreeTwoThreeSpectrum2887.graph fusedMap1702=true := by decide +kernel
theorem certified1702 : Certified (graph core1702) (root 10) 0 2 :=
  of_native_maps core1702 DegreeTwoThreeSpectrum3702.graph DegreeTwoThreeSpectrum2887.graph
    sourceMap1702 fusedMap1702 sourceMap1702_checked fusedMap1702_checked
    DegreeTwoThreeFiniteComparisons.comparison1702
#print axioms sourceMap1702_checked
#print axioms fusedMap1702_checked
#print axioms certified1702
def sourceMap1702swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1702swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1702swap_checked : acceptsGraphIso
    (source (graph core1702) (root 10) 2 0) DegreeTwoThreeSpectrum3702.graph sourceMap1702swap=true := by decide +kernel
theorem fusedMap1702swap_checked : acceptsGraphIso
    (fused (graph core1702) (root 10) 2 0) DegreeTwoThreeSpectrum2887.graph fusedMap1702swap=true := by decide +kernel
theorem certified1702swap : Certified (graph core1702) (root 10) 2 0 :=
  of_native_maps core1702 DegreeTwoThreeSpectrum3702.graph DegreeTwoThreeSpectrum2887.graph
    sourceMap1702swap fusedMap1702swap sourceMap1702swap_checked fusedMap1702swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1702
#print axioms sourceMap1702swap_checked
#print axioms fusedMap1702swap_checked
#print axioms certified1702swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
