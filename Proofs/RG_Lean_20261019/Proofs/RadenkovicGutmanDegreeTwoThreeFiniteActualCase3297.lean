/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3297 : Family 9 := level9.get ⟨230,by decide⟩
def sourceMap3297 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3297 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3297_checked : acceptsGraphIso
    (source (graph core3297) (root 9) 0 5) DegreeTwoThreeSpectrum5558.graph sourceMap3297=true := by decide +kernel
theorem fusedMap3297_checked : acceptsGraphIso
    (fused (graph core3297) (root 9) 0 5) DegreeTwoThreeSpectrum5559.graph fusedMap3297=true := by decide +kernel
theorem certified3297 : Certified (graph core3297) (root 9) 0 5 :=
  of_native_maps core3297 DegreeTwoThreeSpectrum5558.graph DegreeTwoThreeSpectrum5559.graph
    sourceMap3297 fusedMap3297 sourceMap3297_checked fusedMap3297_checked
    DegreeTwoThreeFiniteComparisons.comparison3297
#print axioms sourceMap3297_checked
#print axioms fusedMap3297_checked
#print axioms certified3297
def sourceMap3297swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3297swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3297swap_checked : acceptsGraphIso
    (source (graph core3297) (root 9) 5 0) DegreeTwoThreeSpectrum5558.graph sourceMap3297swap=true := by decide +kernel
theorem fusedMap3297swap_checked : acceptsGraphIso
    (fused (graph core3297) (root 9) 5 0) DegreeTwoThreeSpectrum5559.graph fusedMap3297swap=true := by decide +kernel
theorem certified3297swap : Certified (graph core3297) (root 9) 5 0 :=
  of_native_maps core3297 DegreeTwoThreeSpectrum5558.graph DegreeTwoThreeSpectrum5559.graph
    sourceMap3297swap fusedMap3297swap sourceMap3297swap_checked fusedMap3297swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3297
#print axioms sourceMap3297swap_checked
#print axioms fusedMap3297swap_checked
#print axioms certified3297swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
