/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3664 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap3664 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3664 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3664_checked : acceptsGraphIso
    (source (graph core3664) (root 7) 0 7) DegreeTwoThreeSpectrum5035.graph sourceMap3664=true := by decide +kernel
theorem fusedMap3664_checked : acceptsGraphIso
    (fused (graph core3664) (root 7) 0 7) DegreeTwoThreeSpectrum5038.graph fusedMap3664=true := by decide +kernel
theorem certified3664 : Certified (graph core3664) (root 7) 0 7 :=
  of_native_maps core3664 DegreeTwoThreeSpectrum5035.graph DegreeTwoThreeSpectrum5038.graph
    sourceMap3664 fusedMap3664 sourceMap3664_checked fusedMap3664_checked
    DegreeTwoThreeFiniteComparisons.comparison3664
#print axioms sourceMap3664_checked
#print axioms fusedMap3664_checked
#print axioms certified3664
def sourceMap3664swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3664swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3664swap_checked : acceptsGraphIso
    (source (graph core3664) (root 7) 7 0) DegreeTwoThreeSpectrum5035.graph sourceMap3664swap=true := by decide +kernel
theorem fusedMap3664swap_checked : acceptsGraphIso
    (fused (graph core3664) (root 7) 7 0) DegreeTwoThreeSpectrum5038.graph fusedMap3664swap=true := by decide +kernel
theorem certified3664swap : Certified (graph core3664) (root 7) 7 0 :=
  of_native_maps core3664 DegreeTwoThreeSpectrum5035.graph DegreeTwoThreeSpectrum5038.graph
    sourceMap3664swap fusedMap3664swap sourceMap3664swap_checked fusedMap3664swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3664
#print axioms sourceMap3664swap_checked
#print axioms fusedMap3664swap_checked
#print axioms certified3664swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
