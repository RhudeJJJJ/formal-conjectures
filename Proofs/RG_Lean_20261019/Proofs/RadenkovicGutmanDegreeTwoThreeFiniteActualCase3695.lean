/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3695 : Family 7 := level7.get ⟨95,by decide⟩
def sourceMap3695 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3695 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3695_checked : acceptsGraphIso
    (source (graph core3695) (root 7) 0 7) DegreeTwoThreeSpectrum5672.graph sourceMap3695=true := by decide +kernel
theorem fusedMap3695_checked : acceptsGraphIso
    (fused (graph core3695) (root 7) 0 7) DegreeTwoThreeSpectrum5675.graph fusedMap3695=true := by decide +kernel
theorem certified3695 : Certified (graph core3695) (root 7) 0 7 :=
  of_native_maps core3695 DegreeTwoThreeSpectrum5672.graph DegreeTwoThreeSpectrum5675.graph
    sourceMap3695 fusedMap3695 sourceMap3695_checked fusedMap3695_checked
    DegreeTwoThreeFiniteComparisons.comparison3695
#print axioms sourceMap3695_checked
#print axioms fusedMap3695_checked
#print axioms certified3695
def sourceMap3695swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3695swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3695swap_checked : acceptsGraphIso
    (source (graph core3695) (root 7) 7 0) DegreeTwoThreeSpectrum5672.graph sourceMap3695swap=true := by decide +kernel
theorem fusedMap3695swap_checked : acceptsGraphIso
    (fused (graph core3695) (root 7) 7 0) DegreeTwoThreeSpectrum5675.graph fusedMap3695swap=true := by decide +kernel
theorem certified3695swap : Certified (graph core3695) (root 7) 7 0 :=
  of_native_maps core3695 DegreeTwoThreeSpectrum5672.graph DegreeTwoThreeSpectrum5675.graph
    sourceMap3695swap fusedMap3695swap sourceMap3695swap_checked fusedMap3695swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3695
#print axioms sourceMap3695swap_checked
#print axioms fusedMap3695swap_checked
#print axioms certified3695swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
