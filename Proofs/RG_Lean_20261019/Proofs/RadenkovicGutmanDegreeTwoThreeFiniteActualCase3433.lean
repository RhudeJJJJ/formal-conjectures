/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3433 : Family 9 := level9.get ⟨573,by decide⟩
def sourceMap3433 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3433 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3433_checked : acceptsGraphIso
    (source (graph core3433) (root 9) 0 5) DegreeTwoThreeSpectrum6092.graph sourceMap3433=true := by decide +kernel
theorem fusedMap3433_checked : acceptsGraphIso
    (fused (graph core3433) (root 9) 0 5) DegreeTwoThreeSpectrum6093.graph fusedMap3433=true := by decide +kernel
theorem certified3433 : Certified (graph core3433) (root 9) 0 5 :=
  of_native_maps core3433 DegreeTwoThreeSpectrum6092.graph DegreeTwoThreeSpectrum6093.graph
    sourceMap3433 fusedMap3433 sourceMap3433_checked fusedMap3433_checked
    DegreeTwoThreeFiniteComparisons.comparison3433
#print axioms sourceMap3433_checked
#print axioms fusedMap3433_checked
#print axioms certified3433
def sourceMap3433swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3433swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3433swap_checked : acceptsGraphIso
    (source (graph core3433) (root 9) 5 0) DegreeTwoThreeSpectrum6092.graph sourceMap3433swap=true := by decide +kernel
theorem fusedMap3433swap_checked : acceptsGraphIso
    (fused (graph core3433) (root 9) 5 0) DegreeTwoThreeSpectrum6093.graph fusedMap3433swap=true := by decide +kernel
theorem certified3433swap : Certified (graph core3433) (root 9) 5 0 :=
  of_native_maps core3433 DegreeTwoThreeSpectrum6092.graph DegreeTwoThreeSpectrum6093.graph
    sourceMap3433swap fusedMap3433swap sourceMap3433swap_checked fusedMap3433swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3433
#print axioms sourceMap3433swap_checked
#print axioms fusedMap3433swap_checked
#print axioms certified3433swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
