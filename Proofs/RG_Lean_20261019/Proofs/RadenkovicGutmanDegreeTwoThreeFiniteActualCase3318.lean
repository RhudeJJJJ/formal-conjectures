/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3318 : Family 9 := level9.get ⟨284,by decide⟩
def sourceMap3318 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3318 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3318_checked : acceptsGraphIso
    (source (graph core3318) (root 9) 0 5) DegreeTwoThreeSpectrum5800.graph sourceMap3318=true := by decide +kernel
theorem fusedMap3318_checked : acceptsGraphIso
    (fused (graph core3318) (root 9) 0 5) DegreeTwoThreeSpectrum5801.graph fusedMap3318=true := by decide +kernel
theorem certified3318 : Certified (graph core3318) (root 9) 0 5 :=
  of_native_maps core3318 DegreeTwoThreeSpectrum5800.graph DegreeTwoThreeSpectrum5801.graph
    sourceMap3318 fusedMap3318 sourceMap3318_checked fusedMap3318_checked
    DegreeTwoThreeFiniteComparisons.comparison3318
#print axioms sourceMap3318_checked
#print axioms fusedMap3318_checked
#print axioms certified3318
def sourceMap3318swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3318swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3318swap_checked : acceptsGraphIso
    (source (graph core3318) (root 9) 5 0) DegreeTwoThreeSpectrum5800.graph sourceMap3318swap=true := by decide +kernel
theorem fusedMap3318swap_checked : acceptsGraphIso
    (fused (graph core3318) (root 9) 5 0) DegreeTwoThreeSpectrum5801.graph fusedMap3318swap=true := by decide +kernel
theorem certified3318swap : Certified (graph core3318) (root 9) 5 0 :=
  of_native_maps core3318 DegreeTwoThreeSpectrum5800.graph DegreeTwoThreeSpectrum5801.graph
    sourceMap3318swap fusedMap3318swap sourceMap3318swap_checked fusedMap3318swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3318
#print axioms sourceMap3318swap_checked
#print axioms fusedMap3318swap_checked
#print axioms certified3318swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
