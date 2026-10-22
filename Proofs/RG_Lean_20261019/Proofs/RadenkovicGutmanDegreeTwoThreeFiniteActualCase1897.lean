/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1897 : Family 10 := level10.get ⟨1366,by decide⟩
def sourceMap1897 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1897 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1897_checked : acceptsGraphIso
    (source (graph core1897) (root 10) 0 2) DegreeTwoThreeSpectrum3559.graph sourceMap1897=true := by decide +kernel
theorem fusedMap1897_checked : acceptsGraphIso
    (fused (graph core1897) (root 10) 0 2) DegreeTwoThreeSpectrum3563.graph fusedMap1897=true := by decide +kernel
theorem certified1897 : Certified (graph core1897) (root 10) 0 2 :=
  of_native_maps core1897 DegreeTwoThreeSpectrum3559.graph DegreeTwoThreeSpectrum3563.graph
    sourceMap1897 fusedMap1897 sourceMap1897_checked fusedMap1897_checked
    DegreeTwoThreeFiniteComparisons.comparison1897
#print axioms sourceMap1897_checked
#print axioms fusedMap1897_checked
#print axioms certified1897
def sourceMap1897swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1897swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1897swap_checked : acceptsGraphIso
    (source (graph core1897) (root 10) 2 0) DegreeTwoThreeSpectrum3559.graph sourceMap1897swap=true := by decide +kernel
theorem fusedMap1897swap_checked : acceptsGraphIso
    (fused (graph core1897) (root 10) 2 0) DegreeTwoThreeSpectrum3563.graph fusedMap1897swap=true := by decide +kernel
theorem certified1897swap : Certified (graph core1897) (root 10) 2 0 :=
  of_native_maps core1897 DegreeTwoThreeSpectrum3559.graph DegreeTwoThreeSpectrum3563.graph
    sourceMap1897swap fusedMap1897swap sourceMap1897swap_checked fusedMap1897swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1897
#print axioms sourceMap1897swap_checked
#print axioms fusedMap1897swap_checked
#print axioms certified1897swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
