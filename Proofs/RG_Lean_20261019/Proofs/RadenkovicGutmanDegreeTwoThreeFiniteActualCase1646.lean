/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1646 : Family 10 := level10.get ⟨735,by decide⟩
def sourceMap1646 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1646 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1646_checked : acceptsGraphIso
    (source (graph core1646) (root 10) 0 2) DegreeTwoThreeSpectrum3485.graph sourceMap1646=true := by decide +kernel
theorem fusedMap1646_checked : acceptsGraphIso
    (fused (graph core1646) (root 10) 0 2) DegreeTwoThreeSpectrum2697.graph fusedMap1646=true := by decide +kernel
theorem certified1646 : Certified (graph core1646) (root 10) 0 2 :=
  of_native_maps core1646 DegreeTwoThreeSpectrum3485.graph DegreeTwoThreeSpectrum2697.graph
    sourceMap1646 fusedMap1646 sourceMap1646_checked fusedMap1646_checked
    DegreeTwoThreeFiniteComparisons.comparison1646
#print axioms sourceMap1646_checked
#print axioms fusedMap1646_checked
#print axioms certified1646
def sourceMap1646swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1646swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1646swap_checked : acceptsGraphIso
    (source (graph core1646) (root 10) 2 0) DegreeTwoThreeSpectrum3485.graph sourceMap1646swap=true := by decide +kernel
theorem fusedMap1646swap_checked : acceptsGraphIso
    (fused (graph core1646) (root 10) 2 0) DegreeTwoThreeSpectrum2697.graph fusedMap1646swap=true := by decide +kernel
theorem certified1646swap : Certified (graph core1646) (root 10) 2 0 :=
  of_native_maps core1646 DegreeTwoThreeSpectrum3485.graph DegreeTwoThreeSpectrum2697.graph
    sourceMap1646swap fusedMap1646swap sourceMap1646swap_checked fusedMap1646swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1646
#print axioms sourceMap1646swap_checked
#print axioms fusedMap1646swap_checked
#print axioms certified1646swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
