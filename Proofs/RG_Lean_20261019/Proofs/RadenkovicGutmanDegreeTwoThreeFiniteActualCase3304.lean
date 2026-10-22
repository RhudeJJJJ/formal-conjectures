/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3304 : Family 9 := level9.get ⟨247,by decide⟩
def sourceMap3304 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3304 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3304_checked : acceptsGraphIso
    (source (graph core3304) (root 9) 0 5) DegreeTwoThreeSpectrum5633.graph sourceMap3304=true := by decide +kernel
theorem fusedMap3304_checked : acceptsGraphIso
    (fused (graph core3304) (root 9) 0 5) DegreeTwoThreeSpectrum5634.graph fusedMap3304=true := by decide +kernel
theorem certified3304 : Certified (graph core3304) (root 9) 0 5 :=
  of_native_maps core3304 DegreeTwoThreeSpectrum5633.graph DegreeTwoThreeSpectrum5634.graph
    sourceMap3304 fusedMap3304 sourceMap3304_checked fusedMap3304_checked
    DegreeTwoThreeFiniteComparisons.comparison3304
#print axioms sourceMap3304_checked
#print axioms fusedMap3304_checked
#print axioms certified3304
def sourceMap3304swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3304swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3304swap_checked : acceptsGraphIso
    (source (graph core3304) (root 9) 5 0) DegreeTwoThreeSpectrum5633.graph sourceMap3304swap=true := by decide +kernel
theorem fusedMap3304swap_checked : acceptsGraphIso
    (fused (graph core3304) (root 9) 5 0) DegreeTwoThreeSpectrum5634.graph fusedMap3304swap=true := by decide +kernel
theorem certified3304swap : Certified (graph core3304) (root 9) 5 0 :=
  of_native_maps core3304 DegreeTwoThreeSpectrum5633.graph DegreeTwoThreeSpectrum5634.graph
    sourceMap3304swap fusedMap3304swap sourceMap3304swap_checked fusedMap3304swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3304
#print axioms sourceMap3304swap_checked
#print axioms fusedMap3304swap_checked
#print axioms certified3304swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
