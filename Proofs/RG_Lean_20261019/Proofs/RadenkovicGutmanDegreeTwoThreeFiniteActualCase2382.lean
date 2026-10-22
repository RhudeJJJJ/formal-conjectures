/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2382 : Family 9 := level9.get ⟨502,by decide⟩
def sourceMap2382 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2382 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2382_checked : acceptsGraphIso
    (source (graph core2382) (root 9) 0 4) DegreeTwoThreeSpectrum4579.graph sourceMap2382=true := by decide +kernel
theorem fusedMap2382_checked : acceptsGraphIso
    (fused (graph core2382) (root 9) 0 4) DegreeTwoThreeSpectrum4580.graph fusedMap2382=true := by decide +kernel
theorem certified2382 : Certified (graph core2382) (root 9) 0 4 :=
  of_native_maps core2382 DegreeTwoThreeSpectrum4579.graph DegreeTwoThreeSpectrum4580.graph
    sourceMap2382 fusedMap2382 sourceMap2382_checked fusedMap2382_checked
    DegreeTwoThreeFiniteComparisons.comparison2382
#print axioms sourceMap2382_checked
#print axioms fusedMap2382_checked
#print axioms certified2382
def sourceMap2382swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2382swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2382swap_checked : acceptsGraphIso
    (source (graph core2382) (root 9) 4 0) DegreeTwoThreeSpectrum4579.graph sourceMap2382swap=true := by decide +kernel
theorem fusedMap2382swap_checked : acceptsGraphIso
    (fused (graph core2382) (root 9) 4 0) DegreeTwoThreeSpectrum4580.graph fusedMap2382swap=true := by decide +kernel
theorem certified2382swap : Certified (graph core2382) (root 9) 4 0 :=
  of_native_maps core2382 DegreeTwoThreeSpectrum4579.graph DegreeTwoThreeSpectrum4580.graph
    sourceMap2382swap fusedMap2382swap sourceMap2382swap_checked fusedMap2382swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2382
#print axioms sourceMap2382swap_checked
#print axioms fusedMap2382swap_checked
#print axioms certified2382swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
