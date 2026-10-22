/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2398 : Family 9 := level9.get ⟨535,by decide⟩
def sourceMap2398 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2398 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2398_checked : acceptsGraphIso
    (source (graph core2398) (root 9) 0 4) DegreeTwoThreeSpectrum4644.graph sourceMap2398=true := by decide +kernel
theorem fusedMap2398_checked : acceptsGraphIso
    (fused (graph core2398) (root 9) 0 4) DegreeTwoThreeSpectrum4645.graph fusedMap2398=true := by decide +kernel
theorem certified2398 : Certified (graph core2398) (root 9) 0 4 :=
  of_native_maps core2398 DegreeTwoThreeSpectrum4644.graph DegreeTwoThreeSpectrum4645.graph
    sourceMap2398 fusedMap2398 sourceMap2398_checked fusedMap2398_checked
    DegreeTwoThreeFiniteComparisons.comparison2398
#print axioms sourceMap2398_checked
#print axioms fusedMap2398_checked
#print axioms certified2398
def sourceMap2398swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2398swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2398swap_checked : acceptsGraphIso
    (source (graph core2398) (root 9) 4 0) DegreeTwoThreeSpectrum4644.graph sourceMap2398swap=true := by decide +kernel
theorem fusedMap2398swap_checked : acceptsGraphIso
    (fused (graph core2398) (root 9) 4 0) DegreeTwoThreeSpectrum4645.graph fusedMap2398swap=true := by decide +kernel
theorem certified2398swap : Certified (graph core2398) (root 9) 4 0 :=
  of_native_maps core2398 DegreeTwoThreeSpectrum4644.graph DegreeTwoThreeSpectrum4645.graph
    sourceMap2398swap fusedMap2398swap sourceMap2398swap_checked fusedMap2398swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2398
#print axioms sourceMap2398swap_checked
#print axioms fusedMap2398swap_checked
#print axioms certified2398swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
