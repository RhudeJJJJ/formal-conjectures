/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2327 : Family 9 := level9.get ⟨368,by decide⟩
def sourceMap2327 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2327 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2327_checked : acceptsGraphIso
    (source (graph core2327) (root 9) 0 4) DegreeTwoThreeSpectrum4290.graph sourceMap2327=true := by decide +kernel
theorem fusedMap2327_checked : acceptsGraphIso
    (fused (graph core2327) (root 9) 0 4) DegreeTwoThreeSpectrum4291.graph fusedMap2327=true := by decide +kernel
theorem certified2327 : Certified (graph core2327) (root 9) 0 4 :=
  of_native_maps core2327 DegreeTwoThreeSpectrum4290.graph DegreeTwoThreeSpectrum4291.graph
    sourceMap2327 fusedMap2327 sourceMap2327_checked fusedMap2327_checked
    DegreeTwoThreeFiniteComparisons.comparison2327
#print axioms sourceMap2327_checked
#print axioms fusedMap2327_checked
#print axioms certified2327
def sourceMap2327swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2327swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2327swap_checked : acceptsGraphIso
    (source (graph core2327) (root 9) 4 0) DegreeTwoThreeSpectrum4290.graph sourceMap2327swap=true := by decide +kernel
theorem fusedMap2327swap_checked : acceptsGraphIso
    (fused (graph core2327) (root 9) 4 0) DegreeTwoThreeSpectrum4291.graph fusedMap2327swap=true := by decide +kernel
theorem certified2327swap : Certified (graph core2327) (root 9) 4 0 :=
  of_native_maps core2327 DegreeTwoThreeSpectrum4290.graph DegreeTwoThreeSpectrum4291.graph
    sourceMap2327swap fusedMap2327swap sourceMap2327swap_checked fusedMap2327swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2327
#print axioms sourceMap2327swap_checked
#print axioms fusedMap2327swap_checked
#print axioms certified2327swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
