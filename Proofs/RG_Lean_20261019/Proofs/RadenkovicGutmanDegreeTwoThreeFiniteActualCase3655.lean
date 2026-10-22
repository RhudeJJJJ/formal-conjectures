/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3655 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3655 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3655 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3655_checked : acceptsGraphIso
    (source (graph core3655) (root 6) 0 7) DegreeTwoThreeSpectrum4005.graph sourceMap3655=true := by decide +kernel
theorem fusedMap3655_checked : acceptsGraphIso
    (fused (graph core3655) (root 6) 0 7) DegreeTwoThreeSpectrum4008.graph fusedMap3655=true := by decide +kernel
theorem certified3655 : Certified (graph core3655) (root 6) 0 7 :=
  of_native_maps core3655 DegreeTwoThreeSpectrum4005.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap3655 fusedMap3655 sourceMap3655_checked fusedMap3655_checked
    DegreeTwoThreeFiniteComparisons.comparison3655
#print axioms sourceMap3655_checked
#print axioms fusedMap3655_checked
#print axioms certified3655
def sourceMap3655swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3655swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3655swap_checked : acceptsGraphIso
    (source (graph core3655) (root 6) 7 0) DegreeTwoThreeSpectrum4005.graph sourceMap3655swap=true := by decide +kernel
theorem fusedMap3655swap_checked : acceptsGraphIso
    (fused (graph core3655) (root 6) 7 0) DegreeTwoThreeSpectrum4008.graph fusedMap3655swap=true := by decide +kernel
theorem certified3655swap : Certified (graph core3655) (root 6) 7 0 :=
  of_native_maps core3655 DegreeTwoThreeSpectrum4005.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap3655swap fusedMap3655swap sourceMap3655swap_checked fusedMap3655swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3655
#print axioms sourceMap3655swap_checked
#print axioms fusedMap3655swap_checked
#print axioms certified3655swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
