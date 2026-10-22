/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3588 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap3588 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3588 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3588_checked : acceptsGraphIso
    (source (graph core3588) (root 8) 0 6) DegreeTwoThreeSpectrum5603.graph sourceMap3588=true := by decide +kernel
theorem fusedMap3588_checked : acceptsGraphIso
    (fused (graph core3588) (root 8) 0 6) DegreeTwoThreeSpectrum5605.graph fusedMap3588=true := by decide +kernel
theorem certified3588 : Certified (graph core3588) (root 8) 0 6 :=
  of_native_maps core3588 DegreeTwoThreeSpectrum5603.graph DegreeTwoThreeSpectrum5605.graph
    sourceMap3588 fusedMap3588 sourceMap3588_checked fusedMap3588_checked
    DegreeTwoThreeFiniteComparisons.comparison3588
#print axioms sourceMap3588_checked
#print axioms fusedMap3588_checked
#print axioms certified3588
def sourceMap3588swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3588swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3588swap_checked : acceptsGraphIso
    (source (graph core3588) (root 8) 6 0) DegreeTwoThreeSpectrum5603.graph sourceMap3588swap=true := by decide +kernel
theorem fusedMap3588swap_checked : acceptsGraphIso
    (fused (graph core3588) (root 8) 6 0) DegreeTwoThreeSpectrum5605.graph fusedMap3588swap=true := by decide +kernel
theorem certified3588swap : Certified (graph core3588) (root 8) 6 0 :=
  of_native_maps core3588 DegreeTwoThreeSpectrum5603.graph DegreeTwoThreeSpectrum5605.graph
    sourceMap3588swap fusedMap3588swap sourceMap3588swap_checked fusedMap3588swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3588
#print axioms sourceMap3588swap_checked
#print axioms fusedMap3588swap_checked
#print axioms certified3588swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
