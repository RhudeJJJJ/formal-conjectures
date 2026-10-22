/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1302 : Family 9 := level9.get ⟨363,by decide⟩
def sourceMap1302 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1302 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1302_checked : acceptsGraphIso
    (source (graph core1302) (root 9) 0 2) DegreeTwoThreeSpectrum2002.graph sourceMap1302=true := by decide +kernel
theorem fusedMap1302_checked : acceptsGraphIso
    (fused (graph core1302) (root 9) 0 2) DegreeTwoThreeSpectrum2003.graph fusedMap1302=true := by decide +kernel
theorem certified1302 : Certified (graph core1302) (root 9) 0 2 :=
  of_native_maps core1302 DegreeTwoThreeSpectrum2002.graph DegreeTwoThreeSpectrum2003.graph
    sourceMap1302 fusedMap1302 sourceMap1302_checked fusedMap1302_checked
    DegreeTwoThreeFiniteComparisons.comparison1302
#print axioms sourceMap1302_checked
#print axioms fusedMap1302_checked
#print axioms certified1302
def sourceMap1302swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1302swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1302swap_checked : acceptsGraphIso
    (source (graph core1302) (root 9) 2 0) DegreeTwoThreeSpectrum2002.graph sourceMap1302swap=true := by decide +kernel
theorem fusedMap1302swap_checked : acceptsGraphIso
    (fused (graph core1302) (root 9) 2 0) DegreeTwoThreeSpectrum2003.graph fusedMap1302swap=true := by decide +kernel
theorem certified1302swap : Certified (graph core1302) (root 9) 2 0 :=
  of_native_maps core1302 DegreeTwoThreeSpectrum2002.graph DegreeTwoThreeSpectrum2003.graph
    sourceMap1302swap fusedMap1302swap sourceMap1302swap_checked fusedMap1302swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1302
#print axioms sourceMap1302swap_checked
#print axioms fusedMap1302swap_checked
#print axioms certified1302swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
