/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3942 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3942 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3942 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3942_checked : acceptsGraphIso
    (source (graph core3942) (root 6) 1 5) DegreeTwoThreeSpectrum2663.graph sourceMap3942=true := by decide +kernel
theorem fusedMap3942_checked : acceptsGraphIso
    (fused (graph core3942) (root 6) 1 5) DegreeTwoThreeSpectrum2350.graph fusedMap3942=true := by decide +kernel
theorem certified3942 : Certified (graph core3942) (root 6) 1 5 :=
  of_native_maps core3942 DegreeTwoThreeSpectrum2663.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap3942 fusedMap3942 sourceMap3942_checked fusedMap3942_checked
    DegreeTwoThreeFiniteComparisons.comparison3942
#print axioms sourceMap3942_checked
#print axioms fusedMap3942_checked
#print axioms certified3942
def sourceMap3942swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3942swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3942swap_checked : acceptsGraphIso
    (source (graph core3942) (root 6) 5 1) DegreeTwoThreeSpectrum2663.graph sourceMap3942swap=true := by decide +kernel
theorem fusedMap3942swap_checked : acceptsGraphIso
    (fused (graph core3942) (root 6) 5 1) DegreeTwoThreeSpectrum2350.graph fusedMap3942swap=true := by decide +kernel
theorem certified3942swap : Certified (graph core3942) (root 6) 5 1 :=
  of_native_maps core3942 DegreeTwoThreeSpectrum2663.graph DegreeTwoThreeSpectrum2350.graph
    sourceMap3942swap fusedMap3942swap sourceMap3942swap_checked fusedMap3942swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3942
#print axioms sourceMap3942swap_checked
#print axioms fusedMap3942swap_checked
#print axioms certified3942swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
