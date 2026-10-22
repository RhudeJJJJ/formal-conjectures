/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3409 : Family 9 := level9.get ⟨513,by decide⟩
def sourceMap3409 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3409 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3409_checked : acceptsGraphIso
    (source (graph core3409) (root 9) 0 5) DegreeTwoThreeSpectrum6951.graph sourceMap3409=true := by decide +kernel
theorem fusedMap3409_checked : acceptsGraphIso
    (fused (graph core3409) (root 9) 0 5) DegreeTwoThreeSpectrum5737.graph fusedMap3409=true := by decide +kernel
theorem certified3409 : Certified (graph core3409) (root 9) 0 5 :=
  of_native_maps core3409 DegreeTwoThreeSpectrum6951.graph DegreeTwoThreeSpectrum5737.graph
    sourceMap3409 fusedMap3409 sourceMap3409_checked fusedMap3409_checked
    DegreeTwoThreeFiniteComparisons.comparison3409
#print axioms sourceMap3409_checked
#print axioms fusedMap3409_checked
#print axioms certified3409
def sourceMap3409swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3409swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3409swap_checked : acceptsGraphIso
    (source (graph core3409) (root 9) 5 0) DegreeTwoThreeSpectrum6951.graph sourceMap3409swap=true := by decide +kernel
theorem fusedMap3409swap_checked : acceptsGraphIso
    (fused (graph core3409) (root 9) 5 0) DegreeTwoThreeSpectrum5737.graph fusedMap3409swap=true := by decide +kernel
theorem certified3409swap : Certified (graph core3409) (root 9) 5 0 :=
  of_native_maps core3409 DegreeTwoThreeSpectrum6951.graph DegreeTwoThreeSpectrum5737.graph
    sourceMap3409swap fusedMap3409swap sourceMap3409swap_checked fusedMap3409swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3409
#print axioms sourceMap3409swap_checked
#print axioms fusedMap3409swap_checked
#print axioms certified3409swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
