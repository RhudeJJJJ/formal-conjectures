/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3792 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap3792 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,12,13,7,8,9,10,11] (sourceLabel 7 1 4 v)
def fusedMap3792 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3792_checked : acceptsGraphIso
    (source (graph core3792) (root 7) 1 4) DegreeTwoThreeSpectrum2814.graph sourceMap3792=true := by decide +kernel
theorem fusedMap3792_checked : acceptsGraphIso
    (fused (graph core3792) (root 7) 1 4) DegreeTwoThreeSpectrum2374.graph fusedMap3792=true := by decide +kernel
theorem certified3792 : Certified (graph core3792) (root 7) 1 4 :=
  of_native_maps core3792 DegreeTwoThreeSpectrum2814.graph DegreeTwoThreeSpectrum2374.graph
    sourceMap3792 fusedMap3792 sourceMap3792_checked fusedMap3792_checked
    DegreeTwoThreeFiniteComparisons.comparison3792
#print axioms sourceMap3792_checked
#print axioms fusedMap3792_checked
#print axioms certified3792
def sourceMap3792swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,7,8,9,10,11,12,13] (sourceLabel 7 4 1 v)
def fusedMap3792swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3792swap_checked : acceptsGraphIso
    (source (graph core3792) (root 7) 4 1) DegreeTwoThreeSpectrum2814.graph sourceMap3792swap=true := by decide +kernel
theorem fusedMap3792swap_checked : acceptsGraphIso
    (fused (graph core3792) (root 7) 4 1) DegreeTwoThreeSpectrum2374.graph fusedMap3792swap=true := by decide +kernel
theorem certified3792swap : Certified (graph core3792) (root 7) 4 1 :=
  of_native_maps core3792 DegreeTwoThreeSpectrum2814.graph DegreeTwoThreeSpectrum2374.graph
    sourceMap3792swap fusedMap3792swap sourceMap3792swap_checked fusedMap3792swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3792
#print axioms sourceMap3792swap_checked
#print axioms fusedMap3792swap_checked
#print axioms certified3792swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
