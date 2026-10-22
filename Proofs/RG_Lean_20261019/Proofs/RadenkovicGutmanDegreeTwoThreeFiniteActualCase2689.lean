/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2689 : Family 10 := level10.get ⟨793,by decide⟩
def sourceMap2689 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2689 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2689_checked : acceptsGraphIso
    (source (graph core2689) (root 10) 0 4) DegreeTwoThreeSpectrum6739.graph sourceMap2689=true := by decide +kernel
theorem fusedMap2689_checked : acceptsGraphIso
    (fused (graph core2689) (root 10) 0 4) DegreeTwoThreeSpectrum5578.graph fusedMap2689=true := by decide +kernel
theorem certified2689 : Certified (graph core2689) (root 10) 0 4 :=
  of_native_maps core2689 DegreeTwoThreeSpectrum6739.graph DegreeTwoThreeSpectrum5578.graph
    sourceMap2689 fusedMap2689 sourceMap2689_checked fusedMap2689_checked
    DegreeTwoThreeFiniteComparisons.comparison2689
#print axioms sourceMap2689_checked
#print axioms fusedMap2689_checked
#print axioms certified2689
def sourceMap2689swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2689swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2689swap_checked : acceptsGraphIso
    (source (graph core2689) (root 10) 4 0) DegreeTwoThreeSpectrum6739.graph sourceMap2689swap=true := by decide +kernel
theorem fusedMap2689swap_checked : acceptsGraphIso
    (fused (graph core2689) (root 10) 4 0) DegreeTwoThreeSpectrum5578.graph fusedMap2689swap=true := by decide +kernel
theorem certified2689swap : Certified (graph core2689) (root 10) 4 0 :=
  of_native_maps core2689 DegreeTwoThreeSpectrum6739.graph DegreeTwoThreeSpectrum5578.graph
    sourceMap2689swap fusedMap2689swap sourceMap2689swap_checked fusedMap2689swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2689
#print axioms sourceMap2689swap_checked
#print axioms fusedMap2689swap_checked
#print axioms certified2689swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
