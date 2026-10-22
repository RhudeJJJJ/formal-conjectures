/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3673 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap3673 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3673 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3673_checked : acceptsGraphIso
    (source (graph core3673) (root 7) 0 7) DegreeTwoThreeSpectrum5523.graph sourceMap3673=true := by decide +kernel
theorem fusedMap3673_checked : acceptsGraphIso
    (fused (graph core3673) (root 7) 0 7) DegreeTwoThreeSpectrum5016.graph fusedMap3673=true := by decide +kernel
theorem certified3673 : Certified (graph core3673) (root 7) 0 7 :=
  of_native_maps core3673 DegreeTwoThreeSpectrum5523.graph DegreeTwoThreeSpectrum5016.graph
    sourceMap3673 fusedMap3673 sourceMap3673_checked fusedMap3673_checked
    DegreeTwoThreeFiniteComparisons.comparison3673
#print axioms sourceMap3673_checked
#print axioms fusedMap3673_checked
#print axioms certified3673
def sourceMap3673swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3673swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3673swap_checked : acceptsGraphIso
    (source (graph core3673) (root 7) 7 0) DegreeTwoThreeSpectrum5523.graph sourceMap3673swap=true := by decide +kernel
theorem fusedMap3673swap_checked : acceptsGraphIso
    (fused (graph core3673) (root 7) 7 0) DegreeTwoThreeSpectrum5016.graph fusedMap3673swap=true := by decide +kernel
theorem certified3673swap : Certified (graph core3673) (root 7) 7 0 :=
  of_native_maps core3673 DegreeTwoThreeSpectrum5523.graph DegreeTwoThreeSpectrum5016.graph
    sourceMap3673swap fusedMap3673swap sourceMap3673swap_checked fusedMap3673swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3673
#print axioms sourceMap3673swap_checked
#print axioms fusedMap3673swap_checked
#print axioms certified3673swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
