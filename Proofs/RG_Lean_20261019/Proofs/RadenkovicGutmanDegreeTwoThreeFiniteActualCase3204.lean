/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3204 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap3204 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3204 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3204_checked : acceptsGraphIso
    (source (graph core3204) (root 8) 0 5) DegreeTwoThreeSpectrum4195.graph sourceMap3204=true := by decide +kernel
theorem fusedMap3204_checked : acceptsGraphIso
    (fused (graph core3204) (root 8) 0 5) DegreeTwoThreeSpectrum4196.graph fusedMap3204=true := by decide +kernel
theorem certified3204 : Certified (graph core3204) (root 8) 0 5 :=
  of_native_maps core3204 DegreeTwoThreeSpectrum4195.graph DegreeTwoThreeSpectrum4196.graph
    sourceMap3204 fusedMap3204 sourceMap3204_checked fusedMap3204_checked
    DegreeTwoThreeFiniteComparisons.comparison3204
#print axioms sourceMap3204_checked
#print axioms fusedMap3204_checked
#print axioms certified3204
def sourceMap3204swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3204swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3204swap_checked : acceptsGraphIso
    (source (graph core3204) (root 8) 5 0) DegreeTwoThreeSpectrum4195.graph sourceMap3204swap=true := by decide +kernel
theorem fusedMap3204swap_checked : acceptsGraphIso
    (fused (graph core3204) (root 8) 5 0) DegreeTwoThreeSpectrum4196.graph fusedMap3204swap=true := by decide +kernel
theorem certified3204swap : Certified (graph core3204) (root 8) 5 0 :=
  of_native_maps core3204 DegreeTwoThreeSpectrum4195.graph DegreeTwoThreeSpectrum4196.graph
    sourceMap3204swap fusedMap3204swap sourceMap3204swap_checked fusedMap3204swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3204
#print axioms sourceMap3204swap_checked
#print axioms fusedMap3204swap_checked
#print axioms certified3204swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
