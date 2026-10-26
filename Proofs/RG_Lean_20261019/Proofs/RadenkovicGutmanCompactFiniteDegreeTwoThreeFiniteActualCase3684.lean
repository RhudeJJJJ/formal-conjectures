/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3684 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap3684 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3684 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3684_checked : acceptsGraphIso
    (source (graph core3684) (root 7) 0 7) DegreeTwoThreeSpectrum5234.graph sourceMap3684=true := by decide +kernel
theorem fusedMap3684_checked : acceptsGraphIso
    (fused (graph core3684) (root 7) 0 7) DegreeTwoThreeSpectrum5237.graph fusedMap3684=true := by decide +kernel
theorem certified3684 : Certified (graph core3684) (root 7) 0 7 :=
  of_native_maps core3684 DegreeTwoThreeSpectrum5234.graph DegreeTwoThreeSpectrum5237.graph
    sourceMap3684 fusedMap3684 sourceMap3684_checked fusedMap3684_checked
    DegreeTwoThreeFiniteComparisons.comparison3684
#print axioms sourceMap3684_checked
#print axioms fusedMap3684_checked
#print axioms certified3684
def sourceMap3684swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3684swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3684swap_checked : acceptsGraphIso
    (source (graph core3684) (root 7) 7 0) DegreeTwoThreeSpectrum5234.graph sourceMap3684swap=true := by decide +kernel
theorem fusedMap3684swap_checked : acceptsGraphIso
    (fused (graph core3684) (root 7) 7 0) DegreeTwoThreeSpectrum5237.graph fusedMap3684swap=true := by decide +kernel
theorem certified3684swap : Certified (graph core3684) (root 7) 7 0 :=
  of_native_maps core3684 DegreeTwoThreeSpectrum5234.graph DegreeTwoThreeSpectrum5237.graph
    sourceMap3684swap fusedMap3684swap sourceMap3684swap_checked fusedMap3684swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3684
#print axioms sourceMap3684swap_checked
#print axioms fusedMap3684swap_checked
#print axioms certified3684swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
