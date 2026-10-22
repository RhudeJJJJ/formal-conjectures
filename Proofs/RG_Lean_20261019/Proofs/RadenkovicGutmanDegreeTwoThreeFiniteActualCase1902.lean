/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1902 : Family 10 := level10.get ⟨1375,by decide⟩
def sourceMap1902 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1902 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1902_checked : acceptsGraphIso
    (source (graph core1902) (root 10) 0 2) DegreeTwoThreeSpectrum3571.graph sourceMap1902=true := by decide +kernel
theorem fusedMap1902_checked : acceptsGraphIso
    (fused (graph core1902) (root 10) 0 2) DegreeTwoThreeSpectrum3575.graph fusedMap1902=true := by decide +kernel
theorem certified1902 : Certified (graph core1902) (root 10) 0 2 :=
  of_native_maps core1902 DegreeTwoThreeSpectrum3571.graph DegreeTwoThreeSpectrum3575.graph
    sourceMap1902 fusedMap1902 sourceMap1902_checked fusedMap1902_checked
    DegreeTwoThreeFiniteComparisons.comparison1902
#print axioms sourceMap1902_checked
#print axioms fusedMap1902_checked
#print axioms certified1902
def sourceMap1902swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1902swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1902swap_checked : acceptsGraphIso
    (source (graph core1902) (root 10) 2 0) DegreeTwoThreeSpectrum3571.graph sourceMap1902swap=true := by decide +kernel
theorem fusedMap1902swap_checked : acceptsGraphIso
    (fused (graph core1902) (root 10) 2 0) DegreeTwoThreeSpectrum3575.graph fusedMap1902swap=true := by decide +kernel
theorem certified1902swap : Certified (graph core1902) (root 10) 2 0 :=
  of_native_maps core1902 DegreeTwoThreeSpectrum3571.graph DegreeTwoThreeSpectrum3575.graph
    sourceMap1902swap fusedMap1902swap sourceMap1902swap_checked fusedMap1902swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1902
#print axioms sourceMap1902swap_checked
#print axioms fusedMap1902swap_checked
#print axioms certified1902swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
