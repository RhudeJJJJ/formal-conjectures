/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3657 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3657 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3657 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3657_checked : acceptsGraphIso
    (source (graph core3657) (root 6) 0 7) DegreeTwoThreeSpectrum4059.graph sourceMap3657=true := by decide +kernel
theorem fusedMap3657_checked : acceptsGraphIso
    (fused (graph core3657) (root 6) 0 7) DegreeTwoThreeSpectrum4062.graph fusedMap3657=true := by decide +kernel
theorem certified3657 : Certified (graph core3657) (root 6) 0 7 :=
  of_native_maps core3657 DegreeTwoThreeSpectrum4059.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap3657 fusedMap3657 sourceMap3657_checked fusedMap3657_checked
    DegreeTwoThreeFiniteComparisons.comparison3657
#print axioms sourceMap3657_checked
#print axioms fusedMap3657_checked
#print axioms certified3657
def sourceMap3657swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3657swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3657swap_checked : acceptsGraphIso
    (source (graph core3657) (root 6) 7 0) DegreeTwoThreeSpectrum4059.graph sourceMap3657swap=true := by decide +kernel
theorem fusedMap3657swap_checked : acceptsGraphIso
    (fused (graph core3657) (root 6) 7 0) DegreeTwoThreeSpectrum4062.graph fusedMap3657swap=true := by decide +kernel
theorem certified3657swap : Certified (graph core3657) (root 6) 7 0 :=
  of_native_maps core3657 DegreeTwoThreeSpectrum4059.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap3657swap fusedMap3657swap sourceMap3657swap_checked fusedMap3657swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3657
#print axioms sourceMap3657swap_checked
#print axioms fusedMap3657swap_checked
#print axioms certified3657swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
