/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1881 : Family 10 := level10.get ⟨1330,by decide⟩
def sourceMap1881 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1881 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1881_checked : acceptsGraphIso
    (source (graph core1881) (root 10) 0 2) DegreeTwoThreeSpectrum3506.graph sourceMap1881=true := by decide +kernel
theorem fusedMap1881_checked : acceptsGraphIso
    (fused (graph core1881) (root 10) 0 2) DegreeTwoThreeSpectrum3508.graph fusedMap1881=true := by decide +kernel
theorem certified1881 : Certified (graph core1881) (root 10) 0 2 :=
  of_native_maps core1881 DegreeTwoThreeSpectrum3506.graph DegreeTwoThreeSpectrum3508.graph
    sourceMap1881 fusedMap1881 sourceMap1881_checked fusedMap1881_checked
    DegreeTwoThreeFiniteComparisons.comparison1881
#print axioms sourceMap1881_checked
#print axioms fusedMap1881_checked
#print axioms certified1881
def sourceMap1881swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1881swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1881swap_checked : acceptsGraphIso
    (source (graph core1881) (root 10) 2 0) DegreeTwoThreeSpectrum3506.graph sourceMap1881swap=true := by decide +kernel
theorem fusedMap1881swap_checked : acceptsGraphIso
    (fused (graph core1881) (root 10) 2 0) DegreeTwoThreeSpectrum3508.graph fusedMap1881swap=true := by decide +kernel
theorem certified1881swap : Certified (graph core1881) (root 10) 2 0 :=
  of_native_maps core1881 DegreeTwoThreeSpectrum3506.graph DegreeTwoThreeSpectrum3508.graph
    sourceMap1881swap fusedMap1881swap sourceMap1881swap_checked fusedMap1881swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1881
#print axioms sourceMap1881swap_checked
#print axioms fusedMap1881swap_checked
#print axioms certified1881swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
