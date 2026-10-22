/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3407 : Family 9 := level9.get ⟨510,by decide⟩
def sourceMap3407 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3407 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3407_checked : acceptsGraphIso
    (source (graph core3407) (root 9) 0 5) DegreeTwoThreeSpectrum6935.graph sourceMap3407=true := by decide +kernel
theorem fusedMap3407_checked : acceptsGraphIso
    (fused (graph core3407) (root 9) 0 5) DegreeTwoThreeSpectrum5726.graph fusedMap3407=true := by decide +kernel
theorem certified3407 : Certified (graph core3407) (root 9) 0 5 :=
  of_native_maps core3407 DegreeTwoThreeSpectrum6935.graph DegreeTwoThreeSpectrum5726.graph
    sourceMap3407 fusedMap3407 sourceMap3407_checked fusedMap3407_checked
    DegreeTwoThreeFiniteComparisons.comparison3407
#print axioms sourceMap3407_checked
#print axioms fusedMap3407_checked
#print axioms certified3407
def sourceMap3407swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3407swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3407swap_checked : acceptsGraphIso
    (source (graph core3407) (root 9) 5 0) DegreeTwoThreeSpectrum6935.graph sourceMap3407swap=true := by decide +kernel
theorem fusedMap3407swap_checked : acceptsGraphIso
    (fused (graph core3407) (root 9) 5 0) DegreeTwoThreeSpectrum5726.graph fusedMap3407swap=true := by decide +kernel
theorem certified3407swap : Certified (graph core3407) (root 9) 5 0 :=
  of_native_maps core3407 DegreeTwoThreeSpectrum6935.graph DegreeTwoThreeSpectrum5726.graph
    sourceMap3407swap fusedMap3407swap sourceMap3407swap_checked fusedMap3407swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3407
#print axioms sourceMap3407swap_checked
#print axioms fusedMap3407swap_checked
#print axioms certified3407swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
