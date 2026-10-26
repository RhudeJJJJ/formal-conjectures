/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3568 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap3568 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3568 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3568_checked : acceptsGraphIso
    (source (graph core3568) (root 8) 0 6) DegreeTwoThreeSpectrum5203.graph sourceMap3568=true := by decide +kernel
theorem fusedMap3568_checked : acceptsGraphIso
    (fused (graph core3568) (root 8) 0 6) DegreeTwoThreeSpectrum5205.graph fusedMap3568=true := by decide +kernel
theorem certified3568 : Certified (graph core3568) (root 8) 0 6 :=
  of_native_maps core3568 DegreeTwoThreeSpectrum5203.graph DegreeTwoThreeSpectrum5205.graph
    sourceMap3568 fusedMap3568 sourceMap3568_checked fusedMap3568_checked
    DegreeTwoThreeFiniteComparisons.comparison3568
#print axioms sourceMap3568_checked
#print axioms fusedMap3568_checked
#print axioms certified3568
def sourceMap3568swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3568swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3568swap_checked : acceptsGraphIso
    (source (graph core3568) (root 8) 6 0) DegreeTwoThreeSpectrum5203.graph sourceMap3568swap=true := by decide +kernel
theorem fusedMap3568swap_checked : acceptsGraphIso
    (fused (graph core3568) (root 8) 6 0) DegreeTwoThreeSpectrum5205.graph fusedMap3568swap=true := by decide +kernel
theorem certified3568swap : Certified (graph core3568) (root 8) 6 0 :=
  of_native_maps core3568 DegreeTwoThreeSpectrum5203.graph DegreeTwoThreeSpectrum5205.graph
    sourceMap3568swap fusedMap3568swap sourceMap3568swap_checked fusedMap3568swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3568
#print axioms sourceMap3568swap_checked
#print axioms fusedMap3568swap_checked
#print axioms certified3568swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
