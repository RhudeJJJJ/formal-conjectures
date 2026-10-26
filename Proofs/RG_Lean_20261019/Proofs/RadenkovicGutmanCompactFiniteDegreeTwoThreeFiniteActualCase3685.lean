/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3685 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap3685 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3685 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3685_checked : acceptsGraphIso
    (source (graph core3685) (root 7) 0 7) DegreeTwoThreeSpectrum5251.graph sourceMap3685=true := by decide +kernel
theorem fusedMap3685_checked : acceptsGraphIso
    (fused (graph core3685) (root 7) 0 7) DegreeTwoThreeSpectrum5254.graph fusedMap3685=true := by decide +kernel
theorem certified3685 : Certified (graph core3685) (root 7) 0 7 :=
  of_native_maps core3685 DegreeTwoThreeSpectrum5251.graph DegreeTwoThreeSpectrum5254.graph
    sourceMap3685 fusedMap3685 sourceMap3685_checked fusedMap3685_checked
    DegreeTwoThreeFiniteComparisons.comparison3685
#print axioms sourceMap3685_checked
#print axioms fusedMap3685_checked
#print axioms certified3685
def sourceMap3685swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3685swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3685swap_checked : acceptsGraphIso
    (source (graph core3685) (root 7) 7 0) DegreeTwoThreeSpectrum5251.graph sourceMap3685swap=true := by decide +kernel
theorem fusedMap3685swap_checked : acceptsGraphIso
    (fused (graph core3685) (root 7) 7 0) DegreeTwoThreeSpectrum5254.graph fusedMap3685swap=true := by decide +kernel
theorem certified3685swap : Certified (graph core3685) (root 7) 7 0 :=
  of_native_maps core3685 DegreeTwoThreeSpectrum5251.graph DegreeTwoThreeSpectrum5254.graph
    sourceMap3685swap fusedMap3685swap sourceMap3685swap_checked fusedMap3685swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3685
#print axioms sourceMap3685swap_checked
#print axioms fusedMap3685swap_checked
#print axioms certified3685swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
