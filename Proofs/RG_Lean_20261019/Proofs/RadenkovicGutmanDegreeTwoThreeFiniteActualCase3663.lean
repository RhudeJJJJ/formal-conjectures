/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3663 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap3663 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3663 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3663_checked : acceptsGraphIso
    (source (graph core3663) (root 7) 0 7) DegreeTwoThreeSpectrum4995.graph sourceMap3663=true := by decide +kernel
theorem fusedMap3663_checked : acceptsGraphIso
    (fused (graph core3663) (root 7) 0 7) DegreeTwoThreeSpectrum4998.graph fusedMap3663=true := by decide +kernel
theorem certified3663 : Certified (graph core3663) (root 7) 0 7 :=
  of_native_maps core3663 DegreeTwoThreeSpectrum4995.graph DegreeTwoThreeSpectrum4998.graph
    sourceMap3663 fusedMap3663 sourceMap3663_checked fusedMap3663_checked
    DegreeTwoThreeFiniteComparisons.comparison3663
#print axioms sourceMap3663_checked
#print axioms fusedMap3663_checked
#print axioms certified3663
def sourceMap3663swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3663swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3663swap_checked : acceptsGraphIso
    (source (graph core3663) (root 7) 7 0) DegreeTwoThreeSpectrum4995.graph sourceMap3663swap=true := by decide +kernel
theorem fusedMap3663swap_checked : acceptsGraphIso
    (fused (graph core3663) (root 7) 7 0) DegreeTwoThreeSpectrum4998.graph fusedMap3663swap=true := by decide +kernel
theorem certified3663swap : Certified (graph core3663) (root 7) 7 0 :=
  of_native_maps core3663 DegreeTwoThreeSpectrum4995.graph DegreeTwoThreeSpectrum4998.graph
    sourceMap3663swap fusedMap3663swap sourceMap3663swap_checked fusedMap3663swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3663
#print axioms sourceMap3663swap_checked
#print axioms fusedMap3663swap_checked
#print axioms certified3663swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
