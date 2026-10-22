/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2130 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap2130 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 8 0 4 v)
def fusedMap2130 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2130_checked : acceptsGraphIso
    (source (graph core2130) (root 8) 0 4) DegreeTwoThreeSpectrum2645.graph sourceMap2130=true := by decide +kernel
theorem fusedMap2130_checked : acceptsGraphIso
    (fused (graph core2130) (root 8) 0 4) DegreeTwoThreeSpectrum2339.graph fusedMap2130=true := by decide +kernel
theorem certified2130 : Certified (graph core2130) (root 8) 0 4 :=
  of_native_maps core2130 DegreeTwoThreeSpectrum2645.graph DegreeTwoThreeSpectrum2339.graph
    sourceMap2130 fusedMap2130 sourceMap2130_checked fusedMap2130_checked
    DegreeTwoThreeFiniteComparisons.comparison2130
#print axioms sourceMap2130_checked
#print axioms fusedMap2130_checked
#print axioms certified2130
def sourceMap2130swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14] (sourceLabel 8 4 0 v)
def fusedMap2130swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2130swap_checked : acceptsGraphIso
    (source (graph core2130) (root 8) 4 0) DegreeTwoThreeSpectrum2645.graph sourceMap2130swap=true := by decide +kernel
theorem fusedMap2130swap_checked : acceptsGraphIso
    (fused (graph core2130) (root 8) 4 0) DegreeTwoThreeSpectrum2339.graph fusedMap2130swap=true := by decide +kernel
theorem certified2130swap : Certified (graph core2130) (root 8) 4 0 :=
  of_native_maps core2130 DegreeTwoThreeSpectrum2645.graph DegreeTwoThreeSpectrum2339.graph
    sourceMap2130swap fusedMap2130swap sourceMap2130swap_checked fusedMap2130swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2130
#print axioms sourceMap2130swap_checked
#print axioms fusedMap2130swap_checked
#print axioms certified2130swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
