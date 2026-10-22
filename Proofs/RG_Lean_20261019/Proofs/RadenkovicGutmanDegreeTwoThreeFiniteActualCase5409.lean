/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5409 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5409 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,7,8,2,3,4,5,6,0,9,10,11,12,13,14] (sourceLabel 2 4 6 v)
def fusedMap5409 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 4 6 v)
theorem sourceMap5409_checked : acceptsGraphIso
    (source (graph core5409) (root 2) 4 6) DegreeTwoThreeSpectrum2433.graph sourceMap5409=true := by decide +kernel
theorem fusedMap5409_checked : acceptsGraphIso
    (fused (graph core5409) (root 2) 4 6) DegreeTwoThreeSpectrum2309.graph fusedMap5409=true := by decide +kernel
theorem certified5409 : Certified (graph core5409) (root 2) 4 6 :=
  of_native_maps core5409 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5409 fusedMap5409 sourceMap5409_checked fusedMap5409_checked
    DegreeTwoThreeFiniteComparisons.comparison5409
#print axioms sourceMap5409_checked
#print axioms fusedMap5409_checked
#print axioms certified5409
def sourceMap5409swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,7,8,0,9,10,11,12,13,14,2,3,4,5,6] (sourceLabel 2 6 4 v)
def fusedMap5409swap : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 6 4 v)
theorem sourceMap5409swap_checked : acceptsGraphIso
    (source (graph core5409) (root 2) 6 4) DegreeTwoThreeSpectrum2433.graph sourceMap5409swap=true := by decide +kernel
theorem fusedMap5409swap_checked : acceptsGraphIso
    (fused (graph core5409) (root 2) 6 4) DegreeTwoThreeSpectrum2309.graph fusedMap5409swap=true := by decide +kernel
theorem certified5409swap : Certified (graph core5409) (root 2) 6 4 :=
  of_native_maps core5409 DegreeTwoThreeSpectrum2433.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5409swap fusedMap5409swap sourceMap5409swap_checked fusedMap5409swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5409
#print axioms sourceMap5409swap_checked
#print axioms fusedMap5409swap_checked
#print axioms certified5409swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
