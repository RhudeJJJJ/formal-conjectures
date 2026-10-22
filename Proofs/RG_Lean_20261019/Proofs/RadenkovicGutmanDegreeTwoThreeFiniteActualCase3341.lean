/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3341 : Family 9 := level9.get ⟨348,by decide⟩
def sourceMap3341 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3341 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3341_checked : acceptsGraphIso
    (source (graph core3341) (root 9) 0 5) DegreeTwoThreeSpectrum6148.graph sourceMap3341=true := by decide +kernel
theorem fusedMap3341_checked : acceptsGraphIso
    (fused (graph core3341) (root 9) 0 5) DegreeTwoThreeSpectrum5192.graph fusedMap3341=true := by decide +kernel
theorem certified3341 : Certified (graph core3341) (root 9) 0 5 :=
  of_native_maps core3341 DegreeTwoThreeSpectrum6148.graph DegreeTwoThreeSpectrum5192.graph
    sourceMap3341 fusedMap3341 sourceMap3341_checked fusedMap3341_checked
    DegreeTwoThreeFiniteComparisons.comparison3341
#print axioms sourceMap3341_checked
#print axioms fusedMap3341_checked
#print axioms certified3341
def sourceMap3341swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3341swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3341swap_checked : acceptsGraphIso
    (source (graph core3341) (root 9) 5 0) DegreeTwoThreeSpectrum6148.graph sourceMap3341swap=true := by decide +kernel
theorem fusedMap3341swap_checked : acceptsGraphIso
    (fused (graph core3341) (root 9) 5 0) DegreeTwoThreeSpectrum5192.graph fusedMap3341swap=true := by decide +kernel
theorem certified3341swap : Certified (graph core3341) (root 9) 5 0 :=
  of_native_maps core3341 DegreeTwoThreeSpectrum6148.graph DegreeTwoThreeSpectrum5192.graph
    sourceMap3341swap fusedMap3341swap sourceMap3341swap_checked fusedMap3341swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3341
#print axioms sourceMap3341swap_checked
#print axioms fusedMap3341swap_checked
#print axioms certified3341swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
