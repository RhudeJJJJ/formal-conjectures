/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1864 : Family 10 := level10.get ⟨1288,by decide⟩
def sourceMap1864 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1864 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1864_checked : acceptsGraphIso
    (source (graph core1864) (root 10) 0 2) DegreeTwoThreeSpectrum3457.graph sourceMap1864=true := by decide +kernel
theorem fusedMap1864_checked : acceptsGraphIso
    (fused (graph core1864) (root 10) 0 2) DegreeTwoThreeSpectrum3454.graph fusedMap1864=true := by decide +kernel
theorem certified1864 : Certified (graph core1864) (root 10) 0 2 :=
  of_native_maps core1864 DegreeTwoThreeSpectrum3457.graph DegreeTwoThreeSpectrum3454.graph
    sourceMap1864 fusedMap1864 sourceMap1864_checked fusedMap1864_checked
    DegreeTwoThreeFiniteComparisons.comparison1864
#print axioms sourceMap1864_checked
#print axioms fusedMap1864_checked
#print axioms certified1864
def sourceMap1864swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1864swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1864swap_checked : acceptsGraphIso
    (source (graph core1864) (root 10) 2 0) DegreeTwoThreeSpectrum3457.graph sourceMap1864swap=true := by decide +kernel
theorem fusedMap1864swap_checked : acceptsGraphIso
    (fused (graph core1864) (root 10) 2 0) DegreeTwoThreeSpectrum3454.graph fusedMap1864swap=true := by decide +kernel
theorem certified1864swap : Certified (graph core1864) (root 10) 2 0 :=
  of_native_maps core1864 DegreeTwoThreeSpectrum3457.graph DegreeTwoThreeSpectrum3454.graph
    sourceMap1864swap fusedMap1864swap sourceMap1864swap_checked fusedMap1864swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1864
#print axioms sourceMap1864swap_checked
#print axioms fusedMap1864swap_checked
#print axioms certified1864swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
