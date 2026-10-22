/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3824 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap3824 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3824 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3824_checked : acceptsGraphIso
    (source (graph core3824) (root 7) 1 4) DegreeTwoThreeSpectrum3004.graph sourceMap3824=true := by decide +kernel
theorem fusedMap3824_checked : acceptsGraphIso
    (fused (graph core3824) (root 7) 1 4) DegreeTwoThreeSpectrum2437.graph fusedMap3824=true := by decide +kernel
theorem certified3824 : Certified (graph core3824) (root 7) 1 4 :=
  of_native_maps core3824 DegreeTwoThreeSpectrum3004.graph DegreeTwoThreeSpectrum2437.graph
    sourceMap3824 fusedMap3824 sourceMap3824_checked fusedMap3824_checked
    DegreeTwoThreeFiniteComparisons.comparison3824
#print axioms sourceMap3824_checked
#print axioms fusedMap3824_checked
#print axioms certified3824
def sourceMap3824swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3824swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3824swap_checked : acceptsGraphIso
    (source (graph core3824) (root 7) 4 1) DegreeTwoThreeSpectrum3004.graph sourceMap3824swap=true := by decide +kernel
theorem fusedMap3824swap_checked : acceptsGraphIso
    (fused (graph core3824) (root 7) 4 1) DegreeTwoThreeSpectrum2437.graph fusedMap3824swap=true := by decide +kernel
theorem certified3824swap : Certified (graph core3824) (root 7) 4 1 :=
  of_native_maps core3824 DegreeTwoThreeSpectrum3004.graph DegreeTwoThreeSpectrum2437.graph
    sourceMap3824swap fusedMap3824swap sourceMap3824swap_checked fusedMap3824swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3824
#print axioms sourceMap3824swap_checked
#print axioms fusedMap3824swap_checked
#print axioms certified3824swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
