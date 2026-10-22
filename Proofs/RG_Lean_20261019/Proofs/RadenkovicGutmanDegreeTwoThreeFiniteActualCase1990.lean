/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1990 : Family 10 := level10.get ⟨1594,by decide⟩
def sourceMap1990 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1990 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1990_checked : acceptsGraphIso
    (source (graph core1990) (root 10) 0 2) DegreeTwoThreeSpectrum3775.graph sourceMap1990=true := by decide +kernel
theorem fusedMap1990_checked : acceptsGraphIso
    (fused (graph core1990) (root 10) 0 2) DegreeTwoThreeSpectrum3097.graph fusedMap1990=true := by decide +kernel
theorem certified1990 : Certified (graph core1990) (root 10) 0 2 :=
  of_native_maps core1990 DegreeTwoThreeSpectrum3775.graph DegreeTwoThreeSpectrum3097.graph
    sourceMap1990 fusedMap1990 sourceMap1990_checked fusedMap1990_checked
    DegreeTwoThreeFiniteComparisons.comparison1990
#print axioms sourceMap1990_checked
#print axioms fusedMap1990_checked
#print axioms certified1990
def sourceMap1990swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1990swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1990swap_checked : acceptsGraphIso
    (source (graph core1990) (root 10) 2 0) DegreeTwoThreeSpectrum3775.graph sourceMap1990swap=true := by decide +kernel
theorem fusedMap1990swap_checked : acceptsGraphIso
    (fused (graph core1990) (root 10) 2 0) DegreeTwoThreeSpectrum3097.graph fusedMap1990swap=true := by decide +kernel
theorem certified1990swap : Certified (graph core1990) (root 10) 2 0 :=
  of_native_maps core1990 DegreeTwoThreeSpectrum3775.graph DegreeTwoThreeSpectrum3097.graph
    sourceMap1990swap fusedMap1990swap sourceMap1990swap_checked fusedMap1990swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1990
#print axioms sourceMap1990swap_checked
#print axioms fusedMap1990swap_checked
#print axioms certified1990swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
