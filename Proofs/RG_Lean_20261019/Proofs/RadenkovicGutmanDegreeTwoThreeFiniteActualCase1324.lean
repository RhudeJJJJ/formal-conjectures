/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1324 : Family 9 := level9.get ⟨417,by decide⟩
def sourceMap1324 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1324 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1324_checked : acceptsGraphIso
    (source (graph core1324) (root 9) 0 2) DegreeTwoThreeSpectrum2081.graph sourceMap1324=true := by decide +kernel
theorem fusedMap1324_checked : acceptsGraphIso
    (fused (graph core1324) (root 9) 0 2) DegreeTwoThreeSpectrum2082.graph fusedMap1324=true := by decide +kernel
theorem certified1324 : Certified (graph core1324) (root 9) 0 2 :=
  of_native_maps core1324 DegreeTwoThreeSpectrum2081.graph DegreeTwoThreeSpectrum2082.graph
    sourceMap1324 fusedMap1324 sourceMap1324_checked fusedMap1324_checked
    DegreeTwoThreeFiniteComparisons.comparison1324
#print axioms sourceMap1324_checked
#print axioms fusedMap1324_checked
#print axioms certified1324
def sourceMap1324swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1324swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1324swap_checked : acceptsGraphIso
    (source (graph core1324) (root 9) 2 0) DegreeTwoThreeSpectrum2081.graph sourceMap1324swap=true := by decide +kernel
theorem fusedMap1324swap_checked : acceptsGraphIso
    (fused (graph core1324) (root 9) 2 0) DegreeTwoThreeSpectrum2082.graph fusedMap1324swap=true := by decide +kernel
theorem certified1324swap : Certified (graph core1324) (root 9) 2 0 :=
  of_native_maps core1324 DegreeTwoThreeSpectrum2081.graph DegreeTwoThreeSpectrum2082.graph
    sourceMap1324swap fusedMap1324swap sourceMap1324swap_checked fusedMap1324swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1324
#print axioms sourceMap1324swap_checked
#print axioms fusedMap1324swap_checked
#print axioms certified1324swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
