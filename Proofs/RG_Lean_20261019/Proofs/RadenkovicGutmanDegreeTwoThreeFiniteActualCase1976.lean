/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1976 : Family 10 := level10.get ⟨1567,by decide⟩
def sourceMap1976 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1976 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1976_checked : acceptsGraphIso
    (source (graph core1976) (root 10) 0 2) DegreeTwoThreeSpectrum3760.graph sourceMap1976=true := by decide +kernel
theorem fusedMap1976_checked : acceptsGraphIso
    (fused (graph core1976) (root 10) 0 2) DegreeTwoThreeSpectrum3060.graph fusedMap1976=true := by decide +kernel
theorem certified1976 : Certified (graph core1976) (root 10) 0 2 :=
  of_native_maps core1976 DegreeTwoThreeSpectrum3760.graph DegreeTwoThreeSpectrum3060.graph
    sourceMap1976 fusedMap1976 sourceMap1976_checked fusedMap1976_checked
    DegreeTwoThreeFiniteComparisons.comparison1976
#print axioms sourceMap1976_checked
#print axioms fusedMap1976_checked
#print axioms certified1976
def sourceMap1976swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1976swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1976swap_checked : acceptsGraphIso
    (source (graph core1976) (root 10) 2 0) DegreeTwoThreeSpectrum3760.graph sourceMap1976swap=true := by decide +kernel
theorem fusedMap1976swap_checked : acceptsGraphIso
    (fused (graph core1976) (root 10) 2 0) DegreeTwoThreeSpectrum3060.graph fusedMap1976swap=true := by decide +kernel
theorem certified1976swap : Certified (graph core1976) (root 10) 2 0 :=
  of_native_maps core1976 DegreeTwoThreeSpectrum3760.graph DegreeTwoThreeSpectrum3060.graph
    sourceMap1976swap fusedMap1976swap sourceMap1976swap_checked fusedMap1976swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1976
#print axioms sourceMap1976swap_checked
#print axioms fusedMap1976swap_checked
#print axioms certified1976swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
