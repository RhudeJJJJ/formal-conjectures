/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1930 : Family 10 := level10.get ⟨1443,by decide⟩
def sourceMap1930 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1930 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1930_checked : acceptsGraphIso
    (source (graph core1930) (root 10) 0 2) DegreeTwoThreeSpectrum3673.graph sourceMap1930=true := by decide +kernel
theorem fusedMap1930_checked : acceptsGraphIso
    (fused (graph core1930) (root 10) 0 2) DegreeTwoThreeSpectrum3675.graph fusedMap1930=true := by decide +kernel
theorem certified1930 : Certified (graph core1930) (root 10) 0 2 :=
  of_native_maps core1930 DegreeTwoThreeSpectrum3673.graph DegreeTwoThreeSpectrum3675.graph
    sourceMap1930 fusedMap1930 sourceMap1930_checked fusedMap1930_checked
    DegreeTwoThreeFiniteComparisons.comparison1930
#print axioms sourceMap1930_checked
#print axioms fusedMap1930_checked
#print axioms certified1930
def sourceMap1930swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1930swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1930swap_checked : acceptsGraphIso
    (source (graph core1930) (root 10) 2 0) DegreeTwoThreeSpectrum3673.graph sourceMap1930swap=true := by decide +kernel
theorem fusedMap1930swap_checked : acceptsGraphIso
    (fused (graph core1930) (root 10) 2 0) DegreeTwoThreeSpectrum3675.graph fusedMap1930swap=true := by decide +kernel
theorem certified1930swap : Certified (graph core1930) (root 10) 2 0 :=
  of_native_maps core1930 DegreeTwoThreeSpectrum3673.graph DegreeTwoThreeSpectrum3675.graph
    sourceMap1930swap fusedMap1930swap sourceMap1930swap_checked fusedMap1930swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1930
#print axioms sourceMap1930swap_checked
#print axioms fusedMap1930swap_checked
#print axioms certified1930swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
