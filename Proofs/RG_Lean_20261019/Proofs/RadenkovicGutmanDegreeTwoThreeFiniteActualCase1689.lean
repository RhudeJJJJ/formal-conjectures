/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1689 : Family 10 := level10.get ⟨854,by decide⟩
def sourceMap1689 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1689 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1689_checked : acceptsGraphIso
    (source (graph core1689) (root 10) 0 2) DegreeTwoThreeSpectrum3669.graph sourceMap1689=true := by decide +kernel
theorem fusedMap1689_checked : acceptsGraphIso
    (fused (graph core1689) (root 10) 0 2) DegreeTwoThreeSpectrum2841.graph fusedMap1689=true := by decide +kernel
theorem certified1689 : Certified (graph core1689) (root 10) 0 2 :=
  of_native_maps core1689 DegreeTwoThreeSpectrum3669.graph DegreeTwoThreeSpectrum2841.graph
    sourceMap1689 fusedMap1689 sourceMap1689_checked fusedMap1689_checked
    DegreeTwoThreeFiniteComparisons.comparison1689
#print axioms sourceMap1689_checked
#print axioms fusedMap1689_checked
#print axioms certified1689
def sourceMap1689swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1689swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1689swap_checked : acceptsGraphIso
    (source (graph core1689) (root 10) 2 0) DegreeTwoThreeSpectrum3669.graph sourceMap1689swap=true := by decide +kernel
theorem fusedMap1689swap_checked : acceptsGraphIso
    (fused (graph core1689) (root 10) 2 0) DegreeTwoThreeSpectrum2841.graph fusedMap1689swap=true := by decide +kernel
theorem certified1689swap : Certified (graph core1689) (root 10) 2 0 :=
  of_native_maps core1689 DegreeTwoThreeSpectrum3669.graph DegreeTwoThreeSpectrum2841.graph
    sourceMap1689swap fusedMap1689swap sourceMap1689swap_checked fusedMap1689swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1689
#print axioms sourceMap1689swap_checked
#print axioms fusedMap1689swap_checked
#print axioms certified1689swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
