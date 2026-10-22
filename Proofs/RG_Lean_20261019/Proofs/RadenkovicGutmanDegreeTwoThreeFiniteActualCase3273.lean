/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3273 : Family 9 := level9.get ⟨153,by decide⟩
def sourceMap3273 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3273 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3273_checked : acceptsGraphIso
    (source (graph core3273) (root 9) 0 5) DegreeTwoThreeSpectrum5209.graph sourceMap3273=true := by decide +kernel
theorem fusedMap3273_checked : acceptsGraphIso
    (fused (graph core3273) (root 9) 0 5) DegreeTwoThreeSpectrum5210.graph fusedMap3273=true := by decide +kernel
theorem certified3273 : Certified (graph core3273) (root 9) 0 5 :=
  of_native_maps core3273 DegreeTwoThreeSpectrum5209.graph DegreeTwoThreeSpectrum5210.graph
    sourceMap3273 fusedMap3273 sourceMap3273_checked fusedMap3273_checked
    DegreeTwoThreeFiniteComparisons.comparison3273
#print axioms sourceMap3273_checked
#print axioms fusedMap3273_checked
#print axioms certified3273
def sourceMap3273swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3273swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3273swap_checked : acceptsGraphIso
    (source (graph core3273) (root 9) 5 0) DegreeTwoThreeSpectrum5209.graph sourceMap3273swap=true := by decide +kernel
theorem fusedMap3273swap_checked : acceptsGraphIso
    (fused (graph core3273) (root 9) 5 0) DegreeTwoThreeSpectrum5210.graph fusedMap3273swap=true := by decide +kernel
theorem certified3273swap : Certified (graph core3273) (root 9) 5 0 :=
  of_native_maps core3273 DegreeTwoThreeSpectrum5209.graph DegreeTwoThreeSpectrum5210.graph
    sourceMap3273swap fusedMap3273swap sourceMap3273swap_checked fusedMap3273swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3273
#print axioms sourceMap3273swap_checked
#print axioms fusedMap3273swap_checked
#print axioms certified3273swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
