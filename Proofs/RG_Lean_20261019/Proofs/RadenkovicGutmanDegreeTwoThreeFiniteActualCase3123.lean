/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3123 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap3123 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3123 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3123_checked : acceptsGraphIso
    (source (graph core3123) (root 7) 0 5) DegreeTwoThreeSpectrum2464.graph sourceMap3123=true := by decide +kernel
theorem fusedMap3123_checked : acceptsGraphIso
    (fused (graph core3123) (root 7) 0 5) DegreeTwoThreeSpectrum2466.graph fusedMap3123=true := by decide +kernel
theorem certified3123 : Certified (graph core3123) (root 7) 0 5 :=
  of_native_maps core3123 DegreeTwoThreeSpectrum2464.graph DegreeTwoThreeSpectrum2466.graph
    sourceMap3123 fusedMap3123 sourceMap3123_checked fusedMap3123_checked
    DegreeTwoThreeFiniteComparisons.comparison3123
#print axioms sourceMap3123_checked
#print axioms fusedMap3123_checked
#print axioms certified3123
def sourceMap3123swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3123swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3123swap_checked : acceptsGraphIso
    (source (graph core3123) (root 7) 5 0) DegreeTwoThreeSpectrum2464.graph sourceMap3123swap=true := by decide +kernel
theorem fusedMap3123swap_checked : acceptsGraphIso
    (fused (graph core3123) (root 7) 5 0) DegreeTwoThreeSpectrum2466.graph fusedMap3123swap=true := by decide +kernel
theorem certified3123swap : Certified (graph core3123) (root 7) 5 0 :=
  of_native_maps core3123 DegreeTwoThreeSpectrum2464.graph DegreeTwoThreeSpectrum2466.graph
    sourceMap3123swap fusedMap3123swap sourceMap3123swap_checked fusedMap3123swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3123
#print axioms sourceMap3123swap_checked
#print axioms fusedMap3123swap_checked
#print axioms certified3123swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
