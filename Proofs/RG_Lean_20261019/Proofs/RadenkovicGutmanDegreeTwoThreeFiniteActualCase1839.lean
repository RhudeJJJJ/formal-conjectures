/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1839 : Family 10 := level10.get ⟨1223,by decide⟩
def sourceMap1839 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1839 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1839_checked : acceptsGraphIso
    (source (graph core1839) (root 10) 0 2) DegreeTwoThreeSpectrum3370.graph sourceMap1839=true := by decide +kernel
theorem fusedMap1839_checked : acceptsGraphIso
    (fused (graph core1839) (root 10) 0 2) DegreeTwoThreeSpectrum3369.graph fusedMap1839=true := by decide +kernel
theorem certified1839 : Certified (graph core1839) (root 10) 0 2 :=
  of_native_maps core1839 DegreeTwoThreeSpectrum3370.graph DegreeTwoThreeSpectrum3369.graph
    sourceMap1839 fusedMap1839 sourceMap1839_checked fusedMap1839_checked
    DegreeTwoThreeFiniteComparisons.comparison1839
#print axioms sourceMap1839_checked
#print axioms fusedMap1839_checked
#print axioms certified1839
def sourceMap1839swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1839swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1839swap_checked : acceptsGraphIso
    (source (graph core1839) (root 10) 2 0) DegreeTwoThreeSpectrum3370.graph sourceMap1839swap=true := by decide +kernel
theorem fusedMap1839swap_checked : acceptsGraphIso
    (fused (graph core1839) (root 10) 2 0) DegreeTwoThreeSpectrum3369.graph fusedMap1839swap=true := by decide +kernel
theorem certified1839swap : Certified (graph core1839) (root 10) 2 0 :=
  of_native_maps core1839 DegreeTwoThreeSpectrum3370.graph DegreeTwoThreeSpectrum3369.graph
    sourceMap1839swap fusedMap1839swap sourceMap1839swap_checked fusedMap1839swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1839
#print axioms sourceMap1839swap_checked
#print axioms fusedMap1839swap_checked
#print axioms certified1839swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
