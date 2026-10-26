/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3802 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap3802 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3802 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3802_checked : acceptsGraphIso
    (source (graph core3802) (root 7) 1 4) DegreeTwoThreeSpectrum2755.graph sourceMap3802=true := by decide +kernel
theorem fusedMap3802_checked : acceptsGraphIso
    (fused (graph core3802) (root 7) 1 4) DegreeTwoThreeSpectrum2362.graph fusedMap3802=true := by decide +kernel
theorem certified3802 : Certified (graph core3802) (root 7) 1 4 :=
  of_native_maps core3802 DegreeTwoThreeSpectrum2755.graph DegreeTwoThreeSpectrum2362.graph
    sourceMap3802 fusedMap3802 sourceMap3802_checked fusedMap3802_checked
    DegreeTwoThreeFiniteComparisons.comparison3802
#print axioms sourceMap3802_checked
#print axioms fusedMap3802_checked
#print axioms certified3802
def sourceMap3802swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3802swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3802swap_checked : acceptsGraphIso
    (source (graph core3802) (root 7) 4 1) DegreeTwoThreeSpectrum2755.graph sourceMap3802swap=true := by decide +kernel
theorem fusedMap3802swap_checked : acceptsGraphIso
    (fused (graph core3802) (root 7) 4 1) DegreeTwoThreeSpectrum2362.graph fusedMap3802swap=true := by decide +kernel
theorem certified3802swap : Certified (graph core3802) (root 7) 4 1 :=
  of_native_maps core3802 DegreeTwoThreeSpectrum2755.graph DegreeTwoThreeSpectrum2362.graph
    sourceMap3802swap fusedMap3802swap sourceMap3802swap_checked fusedMap3802swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3802
#print axioms sourceMap3802swap_checked
#print axioms fusedMap3802swap_checked
#print axioms certified3802swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
