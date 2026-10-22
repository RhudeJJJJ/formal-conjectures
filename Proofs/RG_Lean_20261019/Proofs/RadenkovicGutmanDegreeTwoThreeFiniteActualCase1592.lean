/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1592 : Family 10 := level10.get ⟨580,by decide⟩
def sourceMap1592 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1592 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1592_checked : acceptsGraphIso
    (source (graph core1592) (root 10) 0 2) DegreeTwoThreeSpectrum3215.graph sourceMap1592=true := by decide +kernel
theorem fusedMap1592_checked : acceptsGraphIso
    (fused (graph core1592) (root 10) 0 2) DegreeTwoThreeSpectrum2521.graph fusedMap1592=true := by decide +kernel
theorem certified1592 : Certified (graph core1592) (root 10) 0 2 :=
  of_native_maps core1592 DegreeTwoThreeSpectrum3215.graph DegreeTwoThreeSpectrum2521.graph
    sourceMap1592 fusedMap1592 sourceMap1592_checked fusedMap1592_checked
    DegreeTwoThreeFiniteComparisons.comparison1592
#print axioms sourceMap1592_checked
#print axioms fusedMap1592_checked
#print axioms certified1592
def sourceMap1592swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1592swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1592swap_checked : acceptsGraphIso
    (source (graph core1592) (root 10) 2 0) DegreeTwoThreeSpectrum3215.graph sourceMap1592swap=true := by decide +kernel
theorem fusedMap1592swap_checked : acceptsGraphIso
    (fused (graph core1592) (root 10) 2 0) DegreeTwoThreeSpectrum2521.graph fusedMap1592swap=true := by decide +kernel
theorem certified1592swap : Certified (graph core1592) (root 10) 2 0 :=
  of_native_maps core1592 DegreeTwoThreeSpectrum3215.graph DegreeTwoThreeSpectrum2521.graph
    sourceMap1592swap fusedMap1592swap sourceMap1592swap_checked fusedMap1592swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1592
#print axioms sourceMap1592swap_checked
#print axioms fusedMap1592swap_checked
#print axioms certified1592swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
