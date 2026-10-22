/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3271 : Family 9 := level9.get ⟨146,by decide⟩
def sourceMap3271 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3271 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3271_checked : acceptsGraphIso
    (source (graph core3271) (root 9) 0 5) DegreeTwoThreeSpectrum5179.graph sourceMap3271=true := by decide +kernel
theorem fusedMap3271_checked : acceptsGraphIso
    (fused (graph core3271) (root 9) 0 5) DegreeTwoThreeSpectrum5180.graph fusedMap3271=true := by decide +kernel
theorem certified3271 : Certified (graph core3271) (root 9) 0 5 :=
  of_native_maps core3271 DegreeTwoThreeSpectrum5179.graph DegreeTwoThreeSpectrum5180.graph
    sourceMap3271 fusedMap3271 sourceMap3271_checked fusedMap3271_checked
    DegreeTwoThreeFiniteComparisons.comparison3271
#print axioms sourceMap3271_checked
#print axioms fusedMap3271_checked
#print axioms certified3271
def sourceMap3271swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3271swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3271swap_checked : acceptsGraphIso
    (source (graph core3271) (root 9) 5 0) DegreeTwoThreeSpectrum5179.graph sourceMap3271swap=true := by decide +kernel
theorem fusedMap3271swap_checked : acceptsGraphIso
    (fused (graph core3271) (root 9) 5 0) DegreeTwoThreeSpectrum5180.graph fusedMap3271swap=true := by decide +kernel
theorem certified3271swap : Certified (graph core3271) (root 9) 5 0 :=
  of_native_maps core3271 DegreeTwoThreeSpectrum5179.graph DegreeTwoThreeSpectrum5180.graph
    sourceMap3271swap fusedMap3271swap sourceMap3271swap_checked fusedMap3271swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3271
#print axioms sourceMap3271swap_checked
#print axioms fusedMap3271swap_checked
#print axioms certified3271swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
