/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3724 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap3724 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3724 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3724_checked : acceptsGraphIso
    (source (graph core3724) (root 6) 0 8) DegreeTwoThreeSpectrum5160.graph sourceMap3724=true := by decide +kernel
theorem fusedMap3724_checked : acceptsGraphIso
    (fused (graph core3724) (root 6) 0 8) DegreeTwoThreeSpectrum5164.graph fusedMap3724=true := by decide +kernel
theorem certified3724 : Certified (graph core3724) (root 6) 0 8 :=
  of_native_maps core3724 DegreeTwoThreeSpectrum5160.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap3724 fusedMap3724 sourceMap3724_checked fusedMap3724_checked
    DegreeTwoThreeFiniteComparisons.comparison3724
#print axioms sourceMap3724_checked
#print axioms fusedMap3724_checked
#print axioms certified3724
def sourceMap3724swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3724swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3724swap_checked : acceptsGraphIso
    (source (graph core3724) (root 6) 8 0) DegreeTwoThreeSpectrum5160.graph sourceMap3724swap=true := by decide +kernel
theorem fusedMap3724swap_checked : acceptsGraphIso
    (fused (graph core3724) (root 6) 8 0) DegreeTwoThreeSpectrum5164.graph fusedMap3724swap=true := by decide +kernel
theorem certified3724swap : Certified (graph core3724) (root 6) 8 0 :=
  of_native_maps core3724 DegreeTwoThreeSpectrum5160.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap3724swap fusedMap3724swap sourceMap3724swap_checked fusedMap3724swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3724
#print axioms sourceMap3724swap_checked
#print axioms fusedMap3724swap_checked
#print axioms certified3724swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
