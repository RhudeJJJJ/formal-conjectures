/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1739 : Family 10 := level10.get ⟨975,by decide⟩
def sourceMap1739 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1739 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1739_checked : acceptsGraphIso
    (source (graph core1739) (root 10) 0 2) DegreeTwoThreeSpectrum2994.graph sourceMap1739=true := by decide +kernel
theorem fusedMap1739_checked : acceptsGraphIso
    (fused (graph core1739) (root 10) 0 2) DegreeTwoThreeSpectrum2993.graph fusedMap1739=true := by decide +kernel
theorem certified1739 : Certified (graph core1739) (root 10) 0 2 :=
  of_native_maps core1739 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2993.graph
    sourceMap1739 fusedMap1739 sourceMap1739_checked fusedMap1739_checked
    DegreeTwoThreeFiniteComparisons.comparison1739
#print axioms sourceMap1739_checked
#print axioms fusedMap1739_checked
#print axioms certified1739
def sourceMap1739swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1739swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1739swap_checked : acceptsGraphIso
    (source (graph core1739) (root 10) 2 0) DegreeTwoThreeSpectrum2994.graph sourceMap1739swap=true := by decide +kernel
theorem fusedMap1739swap_checked : acceptsGraphIso
    (fused (graph core1739) (root 10) 2 0) DegreeTwoThreeSpectrum2993.graph fusedMap1739swap=true := by decide +kernel
theorem certified1739swap : Certified (graph core1739) (root 10) 2 0 :=
  of_native_maps core1739 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2993.graph
    sourceMap1739swap fusedMap1739swap sourceMap1739swap_checked fusedMap1739swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1739
#print axioms sourceMap1739swap_checked
#print axioms fusedMap1739swap_checked
#print axioms certified1739swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
