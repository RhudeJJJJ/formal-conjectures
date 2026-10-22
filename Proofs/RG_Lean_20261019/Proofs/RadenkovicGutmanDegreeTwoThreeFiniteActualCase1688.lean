/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1688 : Family 10 := level10.get ⟨850,by decide⟩
def sourceMap1688 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1688 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1688_checked : acceptsGraphIso
    (source (graph core1688) (root 10) 0 2) DegreeTwoThreeSpectrum3662.graph sourceMap1688=true := by decide +kernel
theorem fusedMap1688_checked : acceptsGraphIso
    (fused (graph core1688) (root 10) 0 2) DegreeTwoThreeSpectrum2839.graph fusedMap1688=true := by decide +kernel
theorem certified1688 : Certified (graph core1688) (root 10) 0 2 :=
  of_native_maps core1688 DegreeTwoThreeSpectrum3662.graph DegreeTwoThreeSpectrum2839.graph
    sourceMap1688 fusedMap1688 sourceMap1688_checked fusedMap1688_checked
    DegreeTwoThreeFiniteComparisons.comparison1688
#print axioms sourceMap1688_checked
#print axioms fusedMap1688_checked
#print axioms certified1688
def sourceMap1688swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1688swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1688swap_checked : acceptsGraphIso
    (source (graph core1688) (root 10) 2 0) DegreeTwoThreeSpectrum3662.graph sourceMap1688swap=true := by decide +kernel
theorem fusedMap1688swap_checked : acceptsGraphIso
    (fused (graph core1688) (root 10) 2 0) DegreeTwoThreeSpectrum2839.graph fusedMap1688swap=true := by decide +kernel
theorem certified1688swap : Certified (graph core1688) (root 10) 2 0 :=
  of_native_maps core1688 DegreeTwoThreeSpectrum3662.graph DegreeTwoThreeSpectrum2839.graph
    sourceMap1688swap fusedMap1688swap sourceMap1688swap_checked fusedMap1688swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1688
#print axioms sourceMap1688swap_checked
#print axioms fusedMap1688swap_checked
#print axioms certified1688swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
