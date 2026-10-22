/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1882 : Family 10 := level10.get ⟨1332,by decide⟩
def sourceMap1882 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1882 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1882_checked : acceptsGraphIso
    (source (graph core1882) (root 10) 0 2) DegreeTwoThreeSpectrum3509.graph sourceMap1882=true := by decide +kernel
theorem fusedMap1882_checked : acceptsGraphIso
    (fused (graph core1882) (root 10) 0 2) DegreeTwoThreeSpectrum3513.graph fusedMap1882=true := by decide +kernel
theorem certified1882 : Certified (graph core1882) (root 10) 0 2 :=
  of_native_maps core1882 DegreeTwoThreeSpectrum3509.graph DegreeTwoThreeSpectrum3513.graph
    sourceMap1882 fusedMap1882 sourceMap1882_checked fusedMap1882_checked
    DegreeTwoThreeFiniteComparisons.comparison1882
#print axioms sourceMap1882_checked
#print axioms fusedMap1882_checked
#print axioms certified1882
def sourceMap1882swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1882swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1882swap_checked : acceptsGraphIso
    (source (graph core1882) (root 10) 2 0) DegreeTwoThreeSpectrum3509.graph sourceMap1882swap=true := by decide +kernel
theorem fusedMap1882swap_checked : acceptsGraphIso
    (fused (graph core1882) (root 10) 2 0) DegreeTwoThreeSpectrum3513.graph fusedMap1882swap=true := by decide +kernel
theorem certified1882swap : Certified (graph core1882) (root 10) 2 0 :=
  of_native_maps core1882 DegreeTwoThreeSpectrum3509.graph DegreeTwoThreeSpectrum3513.graph
    sourceMap1882swap fusedMap1882swap sourceMap1882swap_checked fusedMap1882swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1882
#print axioms sourceMap1882swap_checked
#print axioms fusedMap1882swap_checked
#print axioms certified1882swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
