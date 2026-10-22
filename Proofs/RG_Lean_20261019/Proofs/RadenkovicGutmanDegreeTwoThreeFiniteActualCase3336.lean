/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3336 : Family 9 := level9.get ⟨336,by decide⟩
def sourceMap3336 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3336 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3336_checked : acceptsGraphIso
    (source (graph core3336) (root 9) 0 5) DegreeTwoThreeSpectrum6088.graph sourceMap3336=true := by decide +kernel
theorem fusedMap3336_checked : acceptsGraphIso
    (fused (graph core3336) (root 9) 0 5) DegreeTwoThreeSpectrum5166.graph fusedMap3336=true := by decide +kernel
theorem certified3336 : Certified (graph core3336) (root 9) 0 5 :=
  of_native_maps core3336 DegreeTwoThreeSpectrum6088.graph DegreeTwoThreeSpectrum5166.graph
    sourceMap3336 fusedMap3336 sourceMap3336_checked fusedMap3336_checked
    DegreeTwoThreeFiniteComparisons.comparison3336
#print axioms sourceMap3336_checked
#print axioms fusedMap3336_checked
#print axioms certified3336
def sourceMap3336swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3336swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3336swap_checked : acceptsGraphIso
    (source (graph core3336) (root 9) 5 0) DegreeTwoThreeSpectrum6088.graph sourceMap3336swap=true := by decide +kernel
theorem fusedMap3336swap_checked : acceptsGraphIso
    (fused (graph core3336) (root 9) 5 0) DegreeTwoThreeSpectrum5166.graph fusedMap3336swap=true := by decide +kernel
theorem certified3336swap : Certified (graph core3336) (root 9) 5 0 :=
  of_native_maps core3336 DegreeTwoThreeSpectrum6088.graph DegreeTwoThreeSpectrum5166.graph
    sourceMap3336swap fusedMap3336swap sourceMap3336swap_checked fusedMap3336swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3336
#print axioms sourceMap3336swap_checked
#print axioms fusedMap3336swap_checked
#print axioms certified3336swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
