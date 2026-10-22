/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2413 : Family 9 := level9.get ⟨574,by decide⟩
def sourceMap2413 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2413 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2413_checked : acceptsGraphIso
    (source (graph core2413) (root 9) 0 4) DegreeTwoThreeSpectrum4703.graph sourceMap2413=true := by decide +kernel
theorem fusedMap2413_checked : acceptsGraphIso
    (fused (graph core2413) (root 9) 0 4) DegreeTwoThreeSpectrum4223.graph fusedMap2413=true := by decide +kernel
theorem certified2413 : Certified (graph core2413) (root 9) 0 4 :=
  of_native_maps core2413 DegreeTwoThreeSpectrum4703.graph DegreeTwoThreeSpectrum4223.graph
    sourceMap2413 fusedMap2413 sourceMap2413_checked fusedMap2413_checked
    DegreeTwoThreeFiniteComparisons.comparison2413
#print axioms sourceMap2413_checked
#print axioms fusedMap2413_checked
#print axioms certified2413
def sourceMap2413swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2413swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2413swap_checked : acceptsGraphIso
    (source (graph core2413) (root 9) 4 0) DegreeTwoThreeSpectrum4703.graph sourceMap2413swap=true := by decide +kernel
theorem fusedMap2413swap_checked : acceptsGraphIso
    (fused (graph core2413) (root 9) 4 0) DegreeTwoThreeSpectrum4223.graph fusedMap2413swap=true := by decide +kernel
theorem certified2413swap : Certified (graph core2413) (root 9) 4 0 :=
  of_native_maps core2413 DegreeTwoThreeSpectrum4703.graph DegreeTwoThreeSpectrum4223.graph
    sourceMap2413swap fusedMap2413swap sourceMap2413swap_checked fusedMap2413swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2413
#print axioms sourceMap2413swap_checked
#print axioms fusedMap2413swap_checked
#print axioms certified2413swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
