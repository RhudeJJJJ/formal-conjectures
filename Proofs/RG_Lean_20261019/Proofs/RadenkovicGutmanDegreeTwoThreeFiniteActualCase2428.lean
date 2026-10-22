/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2428 : Family 9 := level9.get ⟨608,by decide⟩
def sourceMap2428 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2428 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2428_checked : acceptsGraphIso
    (source (graph core2428) (root 9) 0 4) DegreeTwoThreeSpectrum4744.graph sourceMap2428=true := by decide +kernel
theorem fusedMap2428_checked : acceptsGraphIso
    (fused (graph core2428) (root 9) 0 4) DegreeTwoThreeSpectrum4303.graph fusedMap2428=true := by decide +kernel
theorem certified2428 : Certified (graph core2428) (root 9) 0 4 :=
  of_native_maps core2428 DegreeTwoThreeSpectrum4744.graph DegreeTwoThreeSpectrum4303.graph
    sourceMap2428 fusedMap2428 sourceMap2428_checked fusedMap2428_checked
    DegreeTwoThreeFiniteComparisons.comparison2428
#print axioms sourceMap2428_checked
#print axioms fusedMap2428_checked
#print axioms certified2428
def sourceMap2428swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2428swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2428swap_checked : acceptsGraphIso
    (source (graph core2428) (root 9) 4 0) DegreeTwoThreeSpectrum4744.graph sourceMap2428swap=true := by decide +kernel
theorem fusedMap2428swap_checked : acceptsGraphIso
    (fused (graph core2428) (root 9) 4 0) DegreeTwoThreeSpectrum4303.graph fusedMap2428swap=true := by decide +kernel
theorem certified2428swap : Certified (graph core2428) (root 9) 4 0 :=
  of_native_maps core2428 DegreeTwoThreeSpectrum4744.graph DegreeTwoThreeSpectrum4303.graph
    sourceMap2428swap fusedMap2428swap sourceMap2428swap_checked fusedMap2428swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2428
#print axioms sourceMap2428swap_checked
#print axioms fusedMap2428swap_checked
#print axioms certified2428swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
