/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3598 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap3598 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3598 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3598_checked : acceptsGraphIso
    (source (graph core3598) (root 8) 0 6) DegreeTwoThreeSpectrum5823.graph sourceMap3598=true := by decide +kernel
theorem fusedMap3598_checked : acceptsGraphIso
    (fused (graph core3598) (root 8) 0 6) DegreeTwoThreeSpectrum5825.graph fusedMap3598=true := by decide +kernel
theorem certified3598 : Certified (graph core3598) (root 8) 0 6 :=
  of_native_maps core3598 DegreeTwoThreeSpectrum5823.graph DegreeTwoThreeSpectrum5825.graph
    sourceMap3598 fusedMap3598 sourceMap3598_checked fusedMap3598_checked
    DegreeTwoThreeFiniteComparisons.comparison3598
#print axioms sourceMap3598_checked
#print axioms fusedMap3598_checked
#print axioms certified3598
def sourceMap3598swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3598swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3598swap_checked : acceptsGraphIso
    (source (graph core3598) (root 8) 6 0) DegreeTwoThreeSpectrum5823.graph sourceMap3598swap=true := by decide +kernel
theorem fusedMap3598swap_checked : acceptsGraphIso
    (fused (graph core3598) (root 8) 6 0) DegreeTwoThreeSpectrum5825.graph fusedMap3598swap=true := by decide +kernel
theorem certified3598swap : Certified (graph core3598) (root 8) 6 0 :=
  of_native_maps core3598 DegreeTwoThreeSpectrum5823.graph DegreeTwoThreeSpectrum5825.graph
    sourceMap3598swap fusedMap3598swap sourceMap3598swap_checked fusedMap3598swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3598
#print axioms sourceMap3598swap_checked
#print axioms fusedMap3598swap_checked
#print axioms certified3598swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
