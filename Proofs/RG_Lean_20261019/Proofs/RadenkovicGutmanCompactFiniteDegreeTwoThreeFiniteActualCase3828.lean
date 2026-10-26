/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3828 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap3828 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3828 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3828_checked : acceptsGraphIso
    (source (graph core3828) (root 8) 1 4) DegreeTwoThreeSpectrum3978.graph sourceMap3828=true := by decide +kernel
theorem fusedMap3828_checked : acceptsGraphIso
    (fused (graph core3828) (root 8) 1 4) DegreeTwoThreeSpectrum3859.graph fusedMap3828=true := by decide +kernel
theorem certified3828 : Certified (graph core3828) (root 8) 1 4 :=
  of_native_maps core3828 DegreeTwoThreeSpectrum3978.graph DegreeTwoThreeSpectrum3859.graph
    sourceMap3828 fusedMap3828 sourceMap3828_checked fusedMap3828_checked
    DegreeTwoThreeFiniteComparisons.comparison3828
#print axioms sourceMap3828_checked
#print axioms fusedMap3828_checked
#print axioms certified3828
def sourceMap3828swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3828swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3828swap_checked : acceptsGraphIso
    (source (graph core3828) (root 8) 4 1) DegreeTwoThreeSpectrum3978.graph sourceMap3828swap=true := by decide +kernel
theorem fusedMap3828swap_checked : acceptsGraphIso
    (fused (graph core3828) (root 8) 4 1) DegreeTwoThreeSpectrum3859.graph fusedMap3828swap=true := by decide +kernel
theorem certified3828swap : Certified (graph core3828) (root 8) 4 1 :=
  of_native_maps core3828 DegreeTwoThreeSpectrum3978.graph DegreeTwoThreeSpectrum3859.graph
    sourceMap3828swap fusedMap3828swap sourceMap3828swap_checked fusedMap3828swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3828
#print axioms sourceMap3828swap_checked
#print axioms fusedMap3828swap_checked
#print axioms certified3828swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
