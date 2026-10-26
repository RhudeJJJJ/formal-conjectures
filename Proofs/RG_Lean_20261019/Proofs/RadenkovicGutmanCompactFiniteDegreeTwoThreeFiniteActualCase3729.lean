/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3729 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3729 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (sourceLabel 4 0 9 v)
def fusedMap3729 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 0 9 v)
theorem sourceMap3729_checked : acceptsGraphIso
    (source (graph core3729) (root 4) 0 9) DegreeTwoThreeSpectrum3926.graph sourceMap3729=true := by decide +kernel
theorem fusedMap3729_checked : acceptsGraphIso
    (fused (graph core3729) (root 4) 0 9) DegreeTwoThreeSpectrum3855.graph fusedMap3729=true := by decide +kernel
theorem certified3729 : Certified (graph core3729) (root 4) 0 9 :=
  of_native_maps core3729 DegreeTwoThreeSpectrum3926.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap3729 fusedMap3729 sourceMap3729_checked fusedMap3729_checked
    DegreeTwoThreeFiniteComparisons.comparison3729
#print axioms sourceMap3729_checked
#print axioms fusedMap3729_checked
#print axioms certified3729
def sourceMap3729swap : (Vertices 4 ⊕ Fin 10 ⊕ Fin 1) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,10,11,12,13,14,15,9] (sourceLabel 4 9 0 v)
def fusedMap3729swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 9 0 v)
theorem sourceMap3729swap_checked : acceptsGraphIso
    (source (graph core3729) (root 4) 9 0) DegreeTwoThreeSpectrum3926.graph sourceMap3729swap=true := by decide +kernel
theorem fusedMap3729swap_checked : acceptsGraphIso
    (fused (graph core3729) (root 4) 9 0) DegreeTwoThreeSpectrum3855.graph fusedMap3729swap=true := by decide +kernel
theorem certified3729swap : Certified (graph core3729) (root 4) 9 0 :=
  of_native_maps core3729 DegreeTwoThreeSpectrum3926.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap3729swap fusedMap3729swap sourceMap3729swap_checked fusedMap3729swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3729
#print axioms sourceMap3729swap_checked
#print axioms fusedMap3729swap_checked
#print axioms certified3729swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
