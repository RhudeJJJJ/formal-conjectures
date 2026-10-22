/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1962 : Family 10 := level10.get ⟨1535,by decide⟩
def sourceMap1962 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1962 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1962_checked : acceptsGraphIso
    (source (graph core1962) (root 10) 0 2) DegreeTwoThreeSpectrum3743.graph sourceMap1962=true := by decide +kernel
theorem fusedMap1962_checked : acceptsGraphIso
    (fused (graph core1962) (root 10) 0 2) DegreeTwoThreeSpectrum3007.graph fusedMap1962=true := by decide +kernel
theorem certified1962 : Certified (graph core1962) (root 10) 0 2 :=
  of_native_maps core1962 DegreeTwoThreeSpectrum3743.graph DegreeTwoThreeSpectrum3007.graph
    sourceMap1962 fusedMap1962 sourceMap1962_checked fusedMap1962_checked
    DegreeTwoThreeFiniteComparisons.comparison1962
#print axioms sourceMap1962_checked
#print axioms fusedMap1962_checked
#print axioms certified1962
def sourceMap1962swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1962swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1962swap_checked : acceptsGraphIso
    (source (graph core1962) (root 10) 2 0) DegreeTwoThreeSpectrum3743.graph sourceMap1962swap=true := by decide +kernel
theorem fusedMap1962swap_checked : acceptsGraphIso
    (fused (graph core1962) (root 10) 2 0) DegreeTwoThreeSpectrum3007.graph fusedMap1962swap=true := by decide +kernel
theorem certified1962swap : Certified (graph core1962) (root 10) 2 0 :=
  of_native_maps core1962 DegreeTwoThreeSpectrum3743.graph DegreeTwoThreeSpectrum3007.graph
    sourceMap1962swap fusedMap1962swap sourceMap1962swap_checked fusedMap1962swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1962
#print axioms sourceMap1962swap_checked
#print axioms fusedMap1962swap_checked
#print axioms certified1962swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
