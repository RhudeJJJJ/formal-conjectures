/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3698 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap3698 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3698 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3698_checked : acceptsGraphIso
    (source (graph core3698) (root 7) 0 7) DegreeTwoThreeSpectrum6049.graph sourceMap3698=true := by decide +kernel
theorem fusedMap3698_checked : acceptsGraphIso
    (fused (graph core3698) (root 7) 0 7) DegreeTwoThreeSpectrum5159.graph fusedMap3698=true := by decide +kernel
theorem certified3698 : Certified (graph core3698) (root 7) 0 7 :=
  of_native_maps core3698 DegreeTwoThreeSpectrum6049.graph DegreeTwoThreeSpectrum5159.graph
    sourceMap3698 fusedMap3698 sourceMap3698_checked fusedMap3698_checked
    DegreeTwoThreeFiniteComparisons.comparison3698
#print axioms sourceMap3698_checked
#print axioms fusedMap3698_checked
#print axioms certified3698
def sourceMap3698swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,12,13,14,15,16,11] (sourceLabel 7 7 0 v)
def fusedMap3698swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3698swap_checked : acceptsGraphIso
    (source (graph core3698) (root 7) 7 0) DegreeTwoThreeSpectrum6049.graph sourceMap3698swap=true := by decide +kernel
theorem fusedMap3698swap_checked : acceptsGraphIso
    (fused (graph core3698) (root 7) 7 0) DegreeTwoThreeSpectrum5159.graph fusedMap3698swap=true := by decide +kernel
theorem certified3698swap : Certified (graph core3698) (root 7) 7 0 :=
  of_native_maps core3698 DegreeTwoThreeSpectrum6049.graph DegreeTwoThreeSpectrum5159.graph
    sourceMap3698swap fusedMap3698swap sourceMap3698swap_checked fusedMap3698swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3698
#print axioms sourceMap3698swap_checked
#print axioms fusedMap3698swap_checked
#print axioms certified3698swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
