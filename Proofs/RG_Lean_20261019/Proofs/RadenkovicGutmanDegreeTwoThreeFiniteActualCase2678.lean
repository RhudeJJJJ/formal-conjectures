/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2678 : Family 10 := level10.get ⟨759,by decide⟩
def sourceMap2678 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2678 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2678_checked : acceptsGraphIso
    (source (graph core2678) (root 10) 0 4) DegreeTwoThreeSpectrum6671.graph sourceMap2678=true := by decide +kernel
theorem fusedMap2678_checked : acceptsGraphIso
    (fused (graph core2678) (root 10) 0 4) DegreeTwoThreeSpectrum5529.graph fusedMap2678=true := by decide +kernel
theorem certified2678 : Certified (graph core2678) (root 10) 0 4 :=
  of_native_maps core2678 DegreeTwoThreeSpectrum6671.graph DegreeTwoThreeSpectrum5529.graph
    sourceMap2678 fusedMap2678 sourceMap2678_checked fusedMap2678_checked
    DegreeTwoThreeFiniteComparisons.comparison2678
#print axioms sourceMap2678_checked
#print axioms fusedMap2678_checked
#print axioms certified2678
def sourceMap2678swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2678swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2678swap_checked : acceptsGraphIso
    (source (graph core2678) (root 10) 4 0) DegreeTwoThreeSpectrum6671.graph sourceMap2678swap=true := by decide +kernel
theorem fusedMap2678swap_checked : acceptsGraphIso
    (fused (graph core2678) (root 10) 4 0) DegreeTwoThreeSpectrum5529.graph fusedMap2678swap=true := by decide +kernel
theorem certified2678swap : Certified (graph core2678) (root 10) 4 0 :=
  of_native_maps core2678 DegreeTwoThreeSpectrum6671.graph DegreeTwoThreeSpectrum5529.graph
    sourceMap2678swap fusedMap2678swap sourceMap2678swap_checked fusedMap2678swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2678
#print axioms sourceMap2678swap_checked
#print axioms fusedMap2678swap_checked
#print axioms certified2678swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
