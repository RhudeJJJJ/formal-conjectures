/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1827 : Family 10 := level10.get ⟨1200,by decide⟩
def sourceMap1827 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1827 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1827_checked : acceptsGraphIso
    (source (graph core1827) (root 10) 0 2) DegreeTwoThreeSpectrum3319.graph sourceMap1827=true := by decide +kernel
theorem fusedMap1827_checked : acceptsGraphIso
    (fused (graph core1827) (root 10) 0 2) DegreeTwoThreeSpectrum3323.graph fusedMap1827=true := by decide +kernel
theorem certified1827 : Certified (graph core1827) (root 10) 0 2 :=
  of_native_maps core1827 DegreeTwoThreeSpectrum3319.graph DegreeTwoThreeSpectrum3323.graph
    sourceMap1827 fusedMap1827 sourceMap1827_checked fusedMap1827_checked
    DegreeTwoThreeFiniteComparisons.comparison1827
#print axioms sourceMap1827_checked
#print axioms fusedMap1827_checked
#print axioms certified1827
def sourceMap1827swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1827swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1827swap_checked : acceptsGraphIso
    (source (graph core1827) (root 10) 2 0) DegreeTwoThreeSpectrum3319.graph sourceMap1827swap=true := by decide +kernel
theorem fusedMap1827swap_checked : acceptsGraphIso
    (fused (graph core1827) (root 10) 2 0) DegreeTwoThreeSpectrum3323.graph fusedMap1827swap=true := by decide +kernel
theorem certified1827swap : Certified (graph core1827) (root 10) 2 0 :=
  of_native_maps core1827 DegreeTwoThreeSpectrum3319.graph DegreeTwoThreeSpectrum3323.graph
    sourceMap1827swap fusedMap1827swap sourceMap1827swap_checked fusedMap1827swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1827
#print axioms sourceMap1827swap_checked
#print axioms fusedMap1827swap_checked
#print axioms certified1827swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
