/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2409 : Family 9 := level9.get ⟨567,by decide⟩
def sourceMap2409 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2409 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2409_checked : acceptsGraphIso
    (source (graph core2409) (root 9) 0 4) DegreeTwoThreeSpectrum4697.graph sourceMap2409=true := by decide +kernel
theorem fusedMap2409_checked : acceptsGraphIso
    (fused (graph core2409) (root 9) 0 4) DegreeTwoThreeSpectrum4211.graph fusedMap2409=true := by decide +kernel
theorem certified2409 : Certified (graph core2409) (root 9) 0 4 :=
  of_native_maps core2409 DegreeTwoThreeSpectrum4697.graph DegreeTwoThreeSpectrum4211.graph
    sourceMap2409 fusedMap2409 sourceMap2409_checked fusedMap2409_checked
    DegreeTwoThreeFiniteComparisons.comparison2409
#print axioms sourceMap2409_checked
#print axioms fusedMap2409_checked
#print axioms certified2409
def sourceMap2409swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2409swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2409swap_checked : acceptsGraphIso
    (source (graph core2409) (root 9) 4 0) DegreeTwoThreeSpectrum4697.graph sourceMap2409swap=true := by decide +kernel
theorem fusedMap2409swap_checked : acceptsGraphIso
    (fused (graph core2409) (root 9) 4 0) DegreeTwoThreeSpectrum4211.graph fusedMap2409swap=true := by decide +kernel
theorem certified2409swap : Certified (graph core2409) (root 9) 4 0 :=
  of_native_maps core2409 DegreeTwoThreeSpectrum4697.graph DegreeTwoThreeSpectrum4211.graph
    sourceMap2409swap fusedMap2409swap sourceMap2409swap_checked fusedMap2409swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2409
#print axioms sourceMap2409swap_checked
#print axioms fusedMap2409swap_checked
#print axioms certified2409swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
