/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1879 : Family 10 := level10.get ⟨1326,by decide⟩
def sourceMap1879 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1879 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1879_checked : acceptsGraphIso
    (source (graph core1879) (root 10) 0 2) DegreeTwoThreeSpectrum3501.graph sourceMap1879=true := by decide +kernel
theorem fusedMap1879_checked : acceptsGraphIso
    (fused (graph core1879) (root 10) 0 2) DegreeTwoThreeSpectrum3503.graph fusedMap1879=true := by decide +kernel
theorem certified1879 : Certified (graph core1879) (root 10) 0 2 :=
  of_native_maps core1879 DegreeTwoThreeSpectrum3501.graph DegreeTwoThreeSpectrum3503.graph
    sourceMap1879 fusedMap1879 sourceMap1879_checked fusedMap1879_checked
    DegreeTwoThreeFiniteComparisons.comparison1879
#print axioms sourceMap1879_checked
#print axioms fusedMap1879_checked
#print axioms certified1879
def sourceMap1879swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1879swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1879swap_checked : acceptsGraphIso
    (source (graph core1879) (root 10) 2 0) DegreeTwoThreeSpectrum3501.graph sourceMap1879swap=true := by decide +kernel
theorem fusedMap1879swap_checked : acceptsGraphIso
    (fused (graph core1879) (root 10) 2 0) DegreeTwoThreeSpectrum3503.graph fusedMap1879swap=true := by decide +kernel
theorem certified1879swap : Certified (graph core1879) (root 10) 2 0 :=
  of_native_maps core1879 DegreeTwoThreeSpectrum3501.graph DegreeTwoThreeSpectrum3503.graph
    sourceMap1879swap fusedMap1879swap sourceMap1879swap_checked fusedMap1879swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1879
#print axioms sourceMap1879swap_checked
#print axioms fusedMap1879swap_checked
#print axioms certified1879swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
