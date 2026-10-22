/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1805 : Family 10 := level10.get ⟨1149,by decide⟩
def sourceMap1805 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1805 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1805_checked : acceptsGraphIso
    (source (graph core1805) (root 10) 0 2) DegreeTwoThreeSpectrum3242.graph sourceMap1805=true := by decide +kernel
theorem fusedMap1805_checked : acceptsGraphIso
    (fused (graph core1805) (root 10) 0 2) DegreeTwoThreeSpectrum3243.graph fusedMap1805=true := by decide +kernel
theorem certified1805 : Certified (graph core1805) (root 10) 0 2 :=
  of_native_maps core1805 DegreeTwoThreeSpectrum3242.graph DegreeTwoThreeSpectrum3243.graph
    sourceMap1805 fusedMap1805 sourceMap1805_checked fusedMap1805_checked
    DegreeTwoThreeFiniteComparisons.comparison1805
#print axioms sourceMap1805_checked
#print axioms fusedMap1805_checked
#print axioms certified1805
def sourceMap1805swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1805swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1805swap_checked : acceptsGraphIso
    (source (graph core1805) (root 10) 2 0) DegreeTwoThreeSpectrum3242.graph sourceMap1805swap=true := by decide +kernel
theorem fusedMap1805swap_checked : acceptsGraphIso
    (fused (graph core1805) (root 10) 2 0) DegreeTwoThreeSpectrum3243.graph fusedMap1805swap=true := by decide +kernel
theorem certified1805swap : Certified (graph core1805) (root 10) 2 0 :=
  of_native_maps core1805 DegreeTwoThreeSpectrum3242.graph DegreeTwoThreeSpectrum3243.graph
    sourceMap1805swap fusedMap1805swap sourceMap1805swap_checked fusedMap1805swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1805
#print axioms sourceMap1805swap_checked
#print axioms fusedMap1805swap_checked
#print axioms certified1805swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
