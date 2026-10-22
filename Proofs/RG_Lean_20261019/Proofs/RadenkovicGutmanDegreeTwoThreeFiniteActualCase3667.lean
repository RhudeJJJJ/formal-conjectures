/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3667 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap3667 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3667 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3667_checked : acceptsGraphIso
    (source (graph core3667) (root 7) 0 7) DegreeTwoThreeSpectrum5108.graph sourceMap3667=true := by decide +kernel
theorem fusedMap3667_checked : acceptsGraphIso
    (fused (graph core3667) (root 7) 0 7) DegreeTwoThreeSpectrum5111.graph fusedMap3667=true := by decide +kernel
theorem certified3667 : Certified (graph core3667) (root 7) 0 7 :=
  of_native_maps core3667 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum5111.graph
    sourceMap3667 fusedMap3667 sourceMap3667_checked fusedMap3667_checked
    DegreeTwoThreeFiniteComparisons.comparison3667
#print axioms sourceMap3667_checked
#print axioms fusedMap3667_checked
#print axioms certified3667
def sourceMap3667swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3667swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3667swap_checked : acceptsGraphIso
    (source (graph core3667) (root 7) 7 0) DegreeTwoThreeSpectrum5108.graph sourceMap3667swap=true := by decide +kernel
theorem fusedMap3667swap_checked : acceptsGraphIso
    (fused (graph core3667) (root 7) 7 0) DegreeTwoThreeSpectrum5111.graph fusedMap3667swap=true := by decide +kernel
theorem certified3667swap : Certified (graph core3667) (root 7) 7 0 :=
  of_native_maps core3667 DegreeTwoThreeSpectrum5108.graph DegreeTwoThreeSpectrum5111.graph
    sourceMap3667swap fusedMap3667swap sourceMap3667swap_checked fusedMap3667swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3667
#print axioms sourceMap3667swap_checked
#print axioms fusedMap3667swap_checked
#print axioms certified3667swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
