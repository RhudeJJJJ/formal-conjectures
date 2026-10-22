/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3670 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap3670 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3670 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3670_checked : acceptsGraphIso
    (source (graph core3670) (root 7) 0 7) DegreeTwoThreeSpectrum5345.graph sourceMap3670=true := by decide +kernel
theorem fusedMap3670_checked : acceptsGraphIso
    (fused (graph core3670) (root 7) 0 7) DegreeTwoThreeSpectrum4983.graph fusedMap3670=true := by decide +kernel
theorem certified3670 : Certified (graph core3670) (root 7) 0 7 :=
  of_native_maps core3670 DegreeTwoThreeSpectrum5345.graph DegreeTwoThreeSpectrum4983.graph
    sourceMap3670 fusedMap3670 sourceMap3670_checked fusedMap3670_checked
    DegreeTwoThreeFiniteComparisons.comparison3670
#print axioms sourceMap3670_checked
#print axioms fusedMap3670_checked
#print axioms certified3670
def sourceMap3670swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3670swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3670swap_checked : acceptsGraphIso
    (source (graph core3670) (root 7) 7 0) DegreeTwoThreeSpectrum5345.graph sourceMap3670swap=true := by decide +kernel
theorem fusedMap3670swap_checked : acceptsGraphIso
    (fused (graph core3670) (root 7) 7 0) DegreeTwoThreeSpectrum4983.graph fusedMap3670swap=true := by decide +kernel
theorem certified3670swap : Certified (graph core3670) (root 7) 7 0 :=
  of_native_maps core3670 DegreeTwoThreeSpectrum5345.graph DegreeTwoThreeSpectrum4983.graph
    sourceMap3670swap fusedMap3670swap sourceMap3670swap_checked fusedMap3670swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3670
#print axioms sourceMap3670swap_checked
#print axioms fusedMap3670swap_checked
#print axioms certified3670swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
