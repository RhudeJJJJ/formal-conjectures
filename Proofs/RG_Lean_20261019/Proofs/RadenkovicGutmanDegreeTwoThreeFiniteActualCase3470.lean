/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3470 : Family 9 := level9.get ⟨678,by decide⟩
def sourceMap3470 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3470 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3470_checked : acceptsGraphIso
    (source (graph core3470) (root 9) 0 5) DegreeTwoThreeSpectrum6866.graph sourceMap3470=true := by decide +kernel
theorem fusedMap3470_checked : acceptsGraphIso
    (fused (graph core3470) (root 9) 0 5) DegreeTwoThreeSpectrum6867.graph fusedMap3470=true := by decide +kernel
theorem certified3470 : Certified (graph core3470) (root 9) 0 5 :=
  of_native_maps core3470 DegreeTwoThreeSpectrum6866.graph DegreeTwoThreeSpectrum6867.graph
    sourceMap3470 fusedMap3470 sourceMap3470_checked fusedMap3470_checked
    DegreeTwoThreeFiniteComparisons.comparison3470
#print axioms sourceMap3470_checked
#print axioms fusedMap3470_checked
#print axioms certified3470
def sourceMap3470swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3470swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3470swap_checked : acceptsGraphIso
    (source (graph core3470) (root 9) 5 0) DegreeTwoThreeSpectrum6866.graph sourceMap3470swap=true := by decide +kernel
theorem fusedMap3470swap_checked : acceptsGraphIso
    (fused (graph core3470) (root 9) 5 0) DegreeTwoThreeSpectrum6867.graph fusedMap3470swap=true := by decide +kernel
theorem certified3470swap : Certified (graph core3470) (root 9) 5 0 :=
  of_native_maps core3470 DegreeTwoThreeSpectrum6866.graph DegreeTwoThreeSpectrum6867.graph
    sourceMap3470swap fusedMap3470swap sourceMap3470swap_checked fusedMap3470swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3470
#print axioms sourceMap3470swap_checked
#print axioms fusedMap3470swap_checked
#print axioms certified3470swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
