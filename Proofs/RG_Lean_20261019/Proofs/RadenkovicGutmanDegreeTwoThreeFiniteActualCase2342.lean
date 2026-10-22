/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2342 : Family 9 := level9.get ⟨403,by decide⟩
def sourceMap2342 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2342 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2342_checked : acceptsGraphIso
    (source (graph core2342) (root 9) 0 4) DegreeTwoThreeSpectrum4361.graph sourceMap2342=true := by decide +kernel
theorem fusedMap2342_checked : acceptsGraphIso
    (fused (graph core2342) (root 9) 0 4) DegreeTwoThreeSpectrum4362.graph fusedMap2342=true := by decide +kernel
theorem certified2342 : Certified (graph core2342) (root 9) 0 4 :=
  of_native_maps core2342 DegreeTwoThreeSpectrum4361.graph DegreeTwoThreeSpectrum4362.graph
    sourceMap2342 fusedMap2342 sourceMap2342_checked fusedMap2342_checked
    DegreeTwoThreeFiniteComparisons.comparison2342
#print axioms sourceMap2342_checked
#print axioms fusedMap2342_checked
#print axioms certified2342
def sourceMap2342swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2342swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2342swap_checked : acceptsGraphIso
    (source (graph core2342) (root 9) 4 0) DegreeTwoThreeSpectrum4361.graph sourceMap2342swap=true := by decide +kernel
theorem fusedMap2342swap_checked : acceptsGraphIso
    (fused (graph core2342) (root 9) 4 0) DegreeTwoThreeSpectrum4362.graph fusedMap2342swap=true := by decide +kernel
theorem certified2342swap : Certified (graph core2342) (root 9) 4 0 :=
  of_native_maps core2342 DegreeTwoThreeSpectrum4361.graph DegreeTwoThreeSpectrum4362.graph
    sourceMap2342swap fusedMap2342swap sourceMap2342swap_checked fusedMap2342swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2342
#print axioms sourceMap2342swap_checked
#print axioms fusedMap2342swap_checked
#print axioms certified2342swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
