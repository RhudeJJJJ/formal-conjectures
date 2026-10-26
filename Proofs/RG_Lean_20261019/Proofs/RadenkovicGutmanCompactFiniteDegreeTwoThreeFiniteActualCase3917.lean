/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3917 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap3917 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3917 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3917_checked : acceptsGraphIso
    (source (graph core3917) (root 8) 1 4) DegreeTwoThreeSpectrum4843.graph sourceMap3917=true := by decide +kernel
theorem fusedMap3917_checked : acceptsGraphIso
    (fused (graph core3917) (root 8) 1 4) DegreeTwoThreeSpectrum4489.graph fusedMap3917=true := by decide +kernel
theorem certified3917 : Certified (graph core3917) (root 8) 1 4 :=
  of_native_maps core3917 DegreeTwoThreeSpectrum4843.graph DegreeTwoThreeSpectrum4489.graph
    sourceMap3917 fusedMap3917 sourceMap3917_checked fusedMap3917_checked
    DegreeTwoThreeFiniteComparisons.comparison3917
#print axioms sourceMap3917_checked
#print axioms fusedMap3917_checked
#print axioms certified3917
def sourceMap3917swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3917swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3917swap_checked : acceptsGraphIso
    (source (graph core3917) (root 8) 4 1) DegreeTwoThreeSpectrum4843.graph sourceMap3917swap=true := by decide +kernel
theorem fusedMap3917swap_checked : acceptsGraphIso
    (fused (graph core3917) (root 8) 4 1) DegreeTwoThreeSpectrum4489.graph fusedMap3917swap=true := by decide +kernel
theorem certified3917swap : Certified (graph core3917) (root 8) 4 1 :=
  of_native_maps core3917 DegreeTwoThreeSpectrum4843.graph DegreeTwoThreeSpectrum4489.graph
    sourceMap3917swap fusedMap3917swap sourceMap3917swap_checked fusedMap3917swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3917
#print axioms sourceMap3917swap_checked
#print axioms fusedMap3917swap_checked
#print axioms certified3917swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
