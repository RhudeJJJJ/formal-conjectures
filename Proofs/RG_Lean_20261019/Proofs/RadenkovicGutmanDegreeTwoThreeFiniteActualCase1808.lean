/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1808 : Family 10 := level10.get ⟨1156,by decide⟩
def sourceMap1808 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1808 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1808_checked : acceptsGraphIso
    (source (graph core1808) (root 10) 0 2) DegreeTwoThreeSpectrum3251.graph sourceMap1808=true := by decide +kernel
theorem fusedMap1808_checked : acceptsGraphIso
    (fused (graph core1808) (root 10) 0 2) DegreeTwoThreeSpectrum3253.graph fusedMap1808=true := by decide +kernel
theorem certified1808 : Certified (graph core1808) (root 10) 0 2 :=
  of_native_maps core1808 DegreeTwoThreeSpectrum3251.graph DegreeTwoThreeSpectrum3253.graph
    sourceMap1808 fusedMap1808 sourceMap1808_checked fusedMap1808_checked
    DegreeTwoThreeFiniteComparisons.comparison1808
#print axioms sourceMap1808_checked
#print axioms fusedMap1808_checked
#print axioms certified1808
def sourceMap1808swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1808swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1808swap_checked : acceptsGraphIso
    (source (graph core1808) (root 10) 2 0) DegreeTwoThreeSpectrum3251.graph sourceMap1808swap=true := by decide +kernel
theorem fusedMap1808swap_checked : acceptsGraphIso
    (fused (graph core1808) (root 10) 2 0) DegreeTwoThreeSpectrum3253.graph fusedMap1808swap=true := by decide +kernel
theorem certified1808swap : Certified (graph core1808) (root 10) 2 0 :=
  of_native_maps core1808 DegreeTwoThreeSpectrum3251.graph DegreeTwoThreeSpectrum3253.graph
    sourceMap1808swap fusedMap1808swap sourceMap1808swap_checked fusedMap1808swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1808
#print axioms sourceMap1808swap_checked
#print axioms fusedMap1808swap_checked
#print axioms certified1808swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
