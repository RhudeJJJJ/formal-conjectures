/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3295 : Family 9 := level9.get ⟨223,by decide⟩
def sourceMap3295 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3295 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3295_checked : acceptsGraphIso
    (source (graph core3295) (root 9) 0 5) DegreeTwoThreeSpectrum5525.graph sourceMap3295=true := by decide +kernel
theorem fusedMap3295_checked : acceptsGraphIso
    (fused (graph core3295) (root 9) 0 5) DegreeTwoThreeSpectrum5526.graph fusedMap3295=true := by decide +kernel
theorem certified3295 : Certified (graph core3295) (root 9) 0 5 :=
  of_native_maps core3295 DegreeTwoThreeSpectrum5525.graph DegreeTwoThreeSpectrum5526.graph
    sourceMap3295 fusedMap3295 sourceMap3295_checked fusedMap3295_checked
    DegreeTwoThreeFiniteComparisons.comparison3295
#print axioms sourceMap3295_checked
#print axioms fusedMap3295_checked
#print axioms certified3295
def sourceMap3295swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3295swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3295swap_checked : acceptsGraphIso
    (source (graph core3295) (root 9) 5 0) DegreeTwoThreeSpectrum5525.graph sourceMap3295swap=true := by decide +kernel
theorem fusedMap3295swap_checked : acceptsGraphIso
    (fused (graph core3295) (root 9) 5 0) DegreeTwoThreeSpectrum5526.graph fusedMap3295swap=true := by decide +kernel
theorem certified3295swap : Certified (graph core3295) (root 9) 5 0 :=
  of_native_maps core3295 DegreeTwoThreeSpectrum5525.graph DegreeTwoThreeSpectrum5526.graph
    sourceMap3295swap fusedMap3295swap sourceMap3295swap_checked fusedMap3295swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3295
#print axioms sourceMap3295swap_checked
#print axioms fusedMap3295swap_checked
#print axioms certified3295swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
