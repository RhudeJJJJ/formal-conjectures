/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2724 : Family 10 := level10.get ⟨886,by decide⟩
def sourceMap2724 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2724 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2724_checked : acceptsGraphIso
    (source (graph core2724) (root 10) 0 4) DegreeTwoThreeSpectrum6955.graph sourceMap2724=true := by decide +kernel
theorem fusedMap2724_checked : acceptsGraphIso
    (fused (graph core2724) (root 10) 0 4) DegreeTwoThreeSpectrum5740.graph fusedMap2724=true := by decide +kernel
theorem certified2724 : Certified (graph core2724) (root 10) 0 4 :=
  of_native_maps core2724 DegreeTwoThreeSpectrum6955.graph DegreeTwoThreeSpectrum5740.graph
    sourceMap2724 fusedMap2724 sourceMap2724_checked fusedMap2724_checked
    DegreeTwoThreeFiniteComparisons.comparison2724
#print axioms sourceMap2724_checked
#print axioms fusedMap2724_checked
#print axioms certified2724
def sourceMap2724swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2724swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2724swap_checked : acceptsGraphIso
    (source (graph core2724) (root 10) 4 0) DegreeTwoThreeSpectrum6955.graph sourceMap2724swap=true := by decide +kernel
theorem fusedMap2724swap_checked : acceptsGraphIso
    (fused (graph core2724) (root 10) 4 0) DegreeTwoThreeSpectrum5740.graph fusedMap2724swap=true := by decide +kernel
theorem certified2724swap : Certified (graph core2724) (root 10) 4 0 :=
  of_native_maps core2724 DegreeTwoThreeSpectrum6955.graph DegreeTwoThreeSpectrum5740.graph
    sourceMap2724swap fusedMap2724swap sourceMap2724swap_checked fusedMap2724swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2724
#print axioms sourceMap2724swap_checked
#print axioms fusedMap2724swap_checked
#print axioms certified2724swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
