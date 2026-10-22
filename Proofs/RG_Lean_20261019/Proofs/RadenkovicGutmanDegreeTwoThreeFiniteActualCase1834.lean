/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1834 : Family 10 := level10.get ⟨1213,by decide⟩
def sourceMap1834 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1834 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1834_checked : acceptsGraphIso
    (source (graph core1834) (root 10) 0 2) DegreeTwoThreeSpectrum3289.graph sourceMap1834=true := by decide +kernel
theorem fusedMap1834_checked : acceptsGraphIso
    (fused (graph core1834) (root 10) 0 2) DegreeTwoThreeSpectrum3345.graph fusedMap1834=true := by decide +kernel
theorem certified1834 : Certified (graph core1834) (root 10) 0 2 :=
  of_native_maps core1834 DegreeTwoThreeSpectrum3289.graph DegreeTwoThreeSpectrum3345.graph
    sourceMap1834 fusedMap1834 sourceMap1834_checked fusedMap1834_checked
    DegreeTwoThreeFiniteComparisons.comparison1834
#print axioms sourceMap1834_checked
#print axioms fusedMap1834_checked
#print axioms certified1834
def sourceMap1834swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1834swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1834swap_checked : acceptsGraphIso
    (source (graph core1834) (root 10) 2 0) DegreeTwoThreeSpectrum3289.graph sourceMap1834swap=true := by decide +kernel
theorem fusedMap1834swap_checked : acceptsGraphIso
    (fused (graph core1834) (root 10) 2 0) DegreeTwoThreeSpectrum3345.graph fusedMap1834swap=true := by decide +kernel
theorem certified1834swap : Certified (graph core1834) (root 10) 2 0 :=
  of_native_maps core1834 DegreeTwoThreeSpectrum3289.graph DegreeTwoThreeSpectrum3345.graph
    sourceMap1834swap fusedMap1834swap sourceMap1834swap_checked fusedMap1834swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1834
#print axioms sourceMap1834swap_checked
#print axioms fusedMap1834swap_checked
#print axioms certified1834swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
