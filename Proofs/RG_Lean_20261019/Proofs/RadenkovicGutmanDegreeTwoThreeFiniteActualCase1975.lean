/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1975 : Family 10 := level10.get ⟨1561,by decide⟩
def sourceMap1975 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1975 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1975_checked : acceptsGraphIso
    (source (graph core1975) (root 10) 0 2) DegreeTwoThreeSpectrum3759.graph sourceMap1975=true := by decide +kernel
theorem fusedMap1975_checked : acceptsGraphIso
    (fused (graph core1975) (root 10) 0 2) DegreeTwoThreeSpectrum3044.graph fusedMap1975=true := by decide +kernel
theorem certified1975 : Certified (graph core1975) (root 10) 0 2 :=
  of_native_maps core1975 DegreeTwoThreeSpectrum3759.graph DegreeTwoThreeSpectrum3044.graph
    sourceMap1975 fusedMap1975 sourceMap1975_checked fusedMap1975_checked
    DegreeTwoThreeFiniteComparisons.comparison1975
#print axioms sourceMap1975_checked
#print axioms fusedMap1975_checked
#print axioms certified1975
def sourceMap1975swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1975swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1975swap_checked : acceptsGraphIso
    (source (graph core1975) (root 10) 2 0) DegreeTwoThreeSpectrum3759.graph sourceMap1975swap=true := by decide +kernel
theorem fusedMap1975swap_checked : acceptsGraphIso
    (fused (graph core1975) (root 10) 2 0) DegreeTwoThreeSpectrum3044.graph fusedMap1975swap=true := by decide +kernel
theorem certified1975swap : Certified (graph core1975) (root 10) 2 0 :=
  of_native_maps core1975 DegreeTwoThreeSpectrum3759.graph DegreeTwoThreeSpectrum3044.graph
    sourceMap1975swap fusedMap1975swap sourceMap1975swap_checked fusedMap1975swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1975
#print axioms sourceMap1975swap_checked
#print axioms fusedMap1975swap_checked
#print axioms certified1975swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
