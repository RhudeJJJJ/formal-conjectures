/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3959 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap3959 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3959 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3959_checked : acceptsGraphIso
    (source (graph core3959) (root 7) 1 5) DegreeTwoThreeSpectrum4380.graph sourceMap3959=true := by decide +kernel
theorem fusedMap3959_checked : acceptsGraphIso
    (fused (graph core3959) (root 7) 1 5) DegreeTwoThreeSpectrum3963.graph fusedMap3959=true := by decide +kernel
theorem certified3959 : Certified (graph core3959) (root 7) 1 5 :=
  of_native_maps core3959 DegreeTwoThreeSpectrum4380.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap3959 fusedMap3959 sourceMap3959_checked fusedMap3959_checked
    DegreeTwoThreeFiniteComparisons.comparison3959
#print axioms sourceMap3959_checked
#print axioms fusedMap3959_checked
#print axioms certified3959
def sourceMap3959swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3959swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3959swap_checked : acceptsGraphIso
    (source (graph core3959) (root 7) 5 1) DegreeTwoThreeSpectrum4380.graph sourceMap3959swap=true := by decide +kernel
theorem fusedMap3959swap_checked : acceptsGraphIso
    (fused (graph core3959) (root 7) 5 1) DegreeTwoThreeSpectrum3963.graph fusedMap3959swap=true := by decide +kernel
theorem certified3959swap : Certified (graph core3959) (root 7) 5 1 :=
  of_native_maps core3959 DegreeTwoThreeSpectrum4380.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap3959swap fusedMap3959swap sourceMap3959swap_checked fusedMap3959swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3959
#print axioms sourceMap3959swap_checked
#print axioms fusedMap3959swap_checked
#print axioms certified3959swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
