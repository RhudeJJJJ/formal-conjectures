/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3400 : Family 9 := level9.get ⟨496,by decide⟩
def sourceMap3400 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3400 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3400_checked : acceptsGraphIso
    (source (graph core3400) (root 9) 0 5) DegreeTwoThreeSpectrum6887.graph sourceMap3400=true := by decide +kernel
theorem fusedMap3400_checked : acceptsGraphIso
    (fused (graph core3400) (root 9) 0 5) DegreeTwoThreeSpectrum5677.graph fusedMap3400=true := by decide +kernel
theorem certified3400 : Certified (graph core3400) (root 9) 0 5 :=
  of_native_maps core3400 DegreeTwoThreeSpectrum6887.graph DegreeTwoThreeSpectrum5677.graph
    sourceMap3400 fusedMap3400 sourceMap3400_checked fusedMap3400_checked
    DegreeTwoThreeFiniteComparisons.comparison3400
#print axioms sourceMap3400_checked
#print axioms fusedMap3400_checked
#print axioms certified3400
def sourceMap3400swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3400swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3400swap_checked : acceptsGraphIso
    (source (graph core3400) (root 9) 5 0) DegreeTwoThreeSpectrum6887.graph sourceMap3400swap=true := by decide +kernel
theorem fusedMap3400swap_checked : acceptsGraphIso
    (fused (graph core3400) (root 9) 5 0) DegreeTwoThreeSpectrum5677.graph fusedMap3400swap=true := by decide +kernel
theorem certified3400swap : Certified (graph core3400) (root 9) 5 0 :=
  of_native_maps core3400 DegreeTwoThreeSpectrum6887.graph DegreeTwoThreeSpectrum5677.graph
    sourceMap3400swap fusedMap3400swap sourceMap3400swap_checked fusedMap3400swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3400
#print axioms sourceMap3400swap_checked
#print axioms fusedMap3400swap_checked
#print axioms certified3400swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
