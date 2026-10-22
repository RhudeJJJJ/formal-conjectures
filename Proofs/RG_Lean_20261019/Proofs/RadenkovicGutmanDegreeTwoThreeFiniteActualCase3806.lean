/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3806 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap3806 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3806 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3806_checked : acceptsGraphIso
    (source (graph core3806) (root 7) 1 4) DegreeTwoThreeSpectrum2917.graph sourceMap3806=true := by decide +kernel
theorem fusedMap3806_checked : acceptsGraphIso
    (fused (graph core3806) (root 7) 1 4) DegreeTwoThreeSpectrum2394.graph fusedMap3806=true := by decide +kernel
theorem certified3806 : Certified (graph core3806) (root 7) 1 4 :=
  of_native_maps core3806 DegreeTwoThreeSpectrum2917.graph DegreeTwoThreeSpectrum2394.graph
    sourceMap3806 fusedMap3806 sourceMap3806_checked fusedMap3806_checked
    DegreeTwoThreeFiniteComparisons.comparison3806
#print axioms sourceMap3806_checked
#print axioms fusedMap3806_checked
#print axioms certified3806
def sourceMap3806swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3806swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3806swap_checked : acceptsGraphIso
    (source (graph core3806) (root 7) 4 1) DegreeTwoThreeSpectrum2917.graph sourceMap3806swap=true := by decide +kernel
theorem fusedMap3806swap_checked : acceptsGraphIso
    (fused (graph core3806) (root 7) 4 1) DegreeTwoThreeSpectrum2394.graph fusedMap3806swap=true := by decide +kernel
theorem certified3806swap : Certified (graph core3806) (root 7) 4 1 :=
  of_native_maps core3806 DegreeTwoThreeSpectrum2917.graph DegreeTwoThreeSpectrum2394.graph
    sourceMap3806swap fusedMap3806swap sourceMap3806swap_checked fusedMap3806swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3806
#print axioms sourceMap3806swap_checked
#print axioms fusedMap3806swap_checked
#print axioms certified3806swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
