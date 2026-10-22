/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2452 : Family 9 := level9.get ⟨693,by decide⟩
def sourceMap2452 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2452 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2452_checked : acceptsGraphIso
    (source (graph core2452) (root 9) 0 4) DegreeTwoThreeSpectrum4670.graph sourceMap2452=true := by decide +kernel
theorem fusedMap2452_checked : acceptsGraphIso
    (fused (graph core2452) (root 9) 0 4) DegreeTwoThreeSpectrum4671.graph fusedMap2452=true := by decide +kernel
theorem certified2452 : Certified (graph core2452) (root 9) 0 4 :=
  of_native_maps core2452 DegreeTwoThreeSpectrum4670.graph DegreeTwoThreeSpectrum4671.graph
    sourceMap2452 fusedMap2452 sourceMap2452_checked fusedMap2452_checked
    DegreeTwoThreeFiniteComparisons.comparison2452
#print axioms sourceMap2452_checked
#print axioms fusedMap2452_checked
#print axioms certified2452
def sourceMap2452swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2452swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2452swap_checked : acceptsGraphIso
    (source (graph core2452) (root 9) 4 0) DegreeTwoThreeSpectrum4670.graph sourceMap2452swap=true := by decide +kernel
theorem fusedMap2452swap_checked : acceptsGraphIso
    (fused (graph core2452) (root 9) 4 0) DegreeTwoThreeSpectrum4671.graph fusedMap2452swap=true := by decide +kernel
theorem certified2452swap : Certified (graph core2452) (root 9) 4 0 :=
  of_native_maps core2452 DegreeTwoThreeSpectrum4670.graph DegreeTwoThreeSpectrum4671.graph
    sourceMap2452swap fusedMap2452swap sourceMap2452swap_checked fusedMap2452swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2452
#print axioms sourceMap2452swap_checked
#print axioms fusedMap2452swap_checked
#print axioms certified2452swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
