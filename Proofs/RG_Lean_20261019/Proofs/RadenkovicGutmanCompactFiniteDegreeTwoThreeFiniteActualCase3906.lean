/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3906 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap3906 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3906 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3906_checked : acceptsGraphIso
    (source (graph core3906) (root 8) 1 4) DegreeTwoThreeSpectrum4769.graph sourceMap3906=true := by decide +kernel
theorem fusedMap3906_checked : acceptsGraphIso
    (fused (graph core3906) (root 8) 1 4) DegreeTwoThreeSpectrum4341.graph fusedMap3906=true := by decide +kernel
theorem certified3906 : Certified (graph core3906) (root 8) 1 4 :=
  of_native_maps core3906 DegreeTwoThreeSpectrum4769.graph DegreeTwoThreeSpectrum4341.graph
    sourceMap3906 fusedMap3906 sourceMap3906_checked fusedMap3906_checked
    DegreeTwoThreeFiniteComparisons.comparison3906
#print axioms sourceMap3906_checked
#print axioms fusedMap3906_checked
#print axioms certified3906
def sourceMap3906swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3906swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3906swap_checked : acceptsGraphIso
    (source (graph core3906) (root 8) 4 1) DegreeTwoThreeSpectrum4769.graph sourceMap3906swap=true := by decide +kernel
theorem fusedMap3906swap_checked : acceptsGraphIso
    (fused (graph core3906) (root 8) 4 1) DegreeTwoThreeSpectrum4341.graph fusedMap3906swap=true := by decide +kernel
theorem certified3906swap : Certified (graph core3906) (root 8) 4 1 :=
  of_native_maps core3906 DegreeTwoThreeSpectrum4769.graph DegreeTwoThreeSpectrum4341.graph
    sourceMap3906swap fusedMap3906swap sourceMap3906swap_checked fusedMap3906swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3906
#print axioms sourceMap3906swap_checked
#print axioms fusedMap3906swap_checked
#print axioms certified3906swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
