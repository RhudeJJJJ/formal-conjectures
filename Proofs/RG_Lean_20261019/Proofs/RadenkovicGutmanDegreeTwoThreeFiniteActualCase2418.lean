/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2418 : Family 9 := level9.get ⟨588,by decide⟩
def sourceMap2418 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2418 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2418_checked : acceptsGraphIso
    (source (graph core2418) (root 9) 0 4) DegreeTwoThreeSpectrum4723.graph sourceMap2418=true := by decide +kernel
theorem fusedMap2418_checked : acceptsGraphIso
    (fused (graph core2418) (root 9) 0 4) DegreeTwoThreeSpectrum4262.graph fusedMap2418=true := by decide +kernel
theorem certified2418 : Certified (graph core2418) (root 9) 0 4 :=
  of_native_maps core2418 DegreeTwoThreeSpectrum4723.graph DegreeTwoThreeSpectrum4262.graph
    sourceMap2418 fusedMap2418 sourceMap2418_checked fusedMap2418_checked
    DegreeTwoThreeFiniteComparisons.comparison2418
#print axioms sourceMap2418_checked
#print axioms fusedMap2418_checked
#print axioms certified2418
def sourceMap2418swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2418swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2418swap_checked : acceptsGraphIso
    (source (graph core2418) (root 9) 4 0) DegreeTwoThreeSpectrum4723.graph sourceMap2418swap=true := by decide +kernel
theorem fusedMap2418swap_checked : acceptsGraphIso
    (fused (graph core2418) (root 9) 4 0) DegreeTwoThreeSpectrum4262.graph fusedMap2418swap=true := by decide +kernel
theorem certified2418swap : Certified (graph core2418) (root 9) 4 0 :=
  of_native_maps core2418 DegreeTwoThreeSpectrum4723.graph DegreeTwoThreeSpectrum4262.graph
    sourceMap2418swap fusedMap2418swap sourceMap2418swap_checked fusedMap2418swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2418
#print axioms sourceMap2418swap_checked
#print axioms fusedMap2418swap_checked
#print axioms certified2418swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
