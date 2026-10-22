/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3287 : Family 9 := level9.get ⟨195,by decide⟩
def sourceMap3287 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3287 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3287_checked : acceptsGraphIso
    (source (graph core3287) (root 9) 0 5) DegreeTwoThreeSpectrum5399.graph sourceMap3287=true := by decide +kernel
theorem fusedMap3287_checked : acceptsGraphIso
    (fused (graph core3287) (root 9) 0 5) DegreeTwoThreeSpectrum5400.graph fusedMap3287=true := by decide +kernel
theorem certified3287 : Certified (graph core3287) (root 9) 0 5 :=
  of_native_maps core3287 DegreeTwoThreeSpectrum5399.graph DegreeTwoThreeSpectrum5400.graph
    sourceMap3287 fusedMap3287 sourceMap3287_checked fusedMap3287_checked
    DegreeTwoThreeFiniteComparisons.comparison3287
#print axioms sourceMap3287_checked
#print axioms fusedMap3287_checked
#print axioms certified3287
def sourceMap3287swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3287swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3287swap_checked : acceptsGraphIso
    (source (graph core3287) (root 9) 5 0) DegreeTwoThreeSpectrum5399.graph sourceMap3287swap=true := by decide +kernel
theorem fusedMap3287swap_checked : acceptsGraphIso
    (fused (graph core3287) (root 9) 5 0) DegreeTwoThreeSpectrum5400.graph fusedMap3287swap=true := by decide +kernel
theorem certified3287swap : Certified (graph core3287) (root 9) 5 0 :=
  of_native_maps core3287 DegreeTwoThreeSpectrum5399.graph DegreeTwoThreeSpectrum5400.graph
    sourceMap3287swap fusedMap3287swap sourceMap3287swap_checked fusedMap3287swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3287
#print axioms sourceMap3287swap_checked
#print axioms fusedMap3287swap_checked
#print axioms certified3287swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
