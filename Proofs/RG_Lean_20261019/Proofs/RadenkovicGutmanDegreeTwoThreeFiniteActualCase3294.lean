/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3294 : Family 9 := level9.get ⟨220,by decide⟩
def sourceMap3294 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3294 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3294_checked : acceptsGraphIso
    (source (graph core3294) (root 9) 0 5) DegreeTwoThreeSpectrum5513.graph sourceMap3294=true := by decide +kernel
theorem fusedMap3294_checked : acceptsGraphIso
    (fused (graph core3294) (root 9) 0 5) DegreeTwoThreeSpectrum5514.graph fusedMap3294=true := by decide +kernel
theorem certified3294 : Certified (graph core3294) (root 9) 0 5 :=
  of_native_maps core3294 DegreeTwoThreeSpectrum5513.graph DegreeTwoThreeSpectrum5514.graph
    sourceMap3294 fusedMap3294 sourceMap3294_checked fusedMap3294_checked
    DegreeTwoThreeFiniteComparisons.comparison3294
#print axioms sourceMap3294_checked
#print axioms fusedMap3294_checked
#print axioms certified3294
def sourceMap3294swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3294swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3294swap_checked : acceptsGraphIso
    (source (graph core3294) (root 9) 5 0) DegreeTwoThreeSpectrum5513.graph sourceMap3294swap=true := by decide +kernel
theorem fusedMap3294swap_checked : acceptsGraphIso
    (fused (graph core3294) (root 9) 5 0) DegreeTwoThreeSpectrum5514.graph fusedMap3294swap=true := by decide +kernel
theorem certified3294swap : Certified (graph core3294) (root 9) 5 0 :=
  of_native_maps core3294 DegreeTwoThreeSpectrum5513.graph DegreeTwoThreeSpectrum5514.graph
    sourceMap3294swap fusedMap3294swap sourceMap3294swap_checked fusedMap3294swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3294
#print axioms sourceMap3294swap_checked
#print axioms fusedMap3294swap_checked
#print axioms certified3294swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
