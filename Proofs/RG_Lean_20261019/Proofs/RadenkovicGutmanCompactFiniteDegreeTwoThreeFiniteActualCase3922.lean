/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3922 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap3922 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3922 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3922_checked : acceptsGraphIso
    (source (graph core3922) (root 8) 1 4) DegreeTwoThreeSpectrum4692.graph sourceMap3922=true := by decide +kernel
theorem fusedMap3922_checked : acceptsGraphIso
    (fused (graph core3922) (root 8) 1 4) DegreeTwoThreeSpectrum4204.graph fusedMap3922=true := by decide +kernel
theorem certified3922 : Certified (graph core3922) (root 8) 1 4 :=
  of_native_maps core3922 DegreeTwoThreeSpectrum4692.graph DegreeTwoThreeSpectrum4204.graph
    sourceMap3922 fusedMap3922 sourceMap3922_checked fusedMap3922_checked
    DegreeTwoThreeFiniteComparisons.comparison3922
#print axioms sourceMap3922_checked
#print axioms fusedMap3922_checked
#print axioms certified3922
def sourceMap3922swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3922swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3922swap_checked : acceptsGraphIso
    (source (graph core3922) (root 8) 4 1) DegreeTwoThreeSpectrum4692.graph sourceMap3922swap=true := by decide +kernel
theorem fusedMap3922swap_checked : acceptsGraphIso
    (fused (graph core3922) (root 8) 4 1) DegreeTwoThreeSpectrum4204.graph fusedMap3922swap=true := by decide +kernel
theorem certified3922swap : Certified (graph core3922) (root 8) 4 1 :=
  of_native_maps core3922 DegreeTwoThreeSpectrum4692.graph DegreeTwoThreeSpectrum4204.graph
    sourceMap3922swap fusedMap3922swap sourceMap3922swap_checked fusedMap3922swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3922
#print axioms sourceMap3922swap_checked
#print axioms fusedMap3922swap_checked
#print axioms certified3922swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
