/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3654 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3654 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3654 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3654_checked : acceptsGraphIso
    (source (graph core3654) (root 6) 0 7) DegreeTwoThreeSpectrum3988.graph sourceMap3654=true := by decide +kernel
theorem fusedMap3654_checked : acceptsGraphIso
    (fused (graph core3654) (root 6) 0 7) DegreeTwoThreeSpectrum3991.graph fusedMap3654=true := by decide +kernel
theorem certified3654 : Certified (graph core3654) (root 6) 0 7 :=
  of_native_maps core3654 DegreeTwoThreeSpectrum3988.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap3654 fusedMap3654 sourceMap3654_checked fusedMap3654_checked
    DegreeTwoThreeFiniteComparisons.comparison3654
#print axioms sourceMap3654_checked
#print axioms fusedMap3654_checked
#print axioms certified3654
def sourceMap3654swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3654swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3654swap_checked : acceptsGraphIso
    (source (graph core3654) (root 6) 7 0) DegreeTwoThreeSpectrum3988.graph sourceMap3654swap=true := by decide +kernel
theorem fusedMap3654swap_checked : acceptsGraphIso
    (fused (graph core3654) (root 6) 7 0) DegreeTwoThreeSpectrum3991.graph fusedMap3654swap=true := by decide +kernel
theorem certified3654swap : Certified (graph core3654) (root 6) 7 0 :=
  of_native_maps core3654 DegreeTwoThreeSpectrum3988.graph DegreeTwoThreeSpectrum3991.graph
    sourceMap3654swap fusedMap3654swap sourceMap3654swap_checked fusedMap3654swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3654
#print axioms sourceMap3654swap_checked
#print axioms fusedMap3654swap_checked
#print axioms certified3654swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
