/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3446 : Family 9 := level9.get ⟨602,by decide⟩
def sourceMap3446 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3446 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3446_checked : acceptsGraphIso
    (source (graph core3446) (root 9) 0 5) DegreeTwoThreeSpectrum6245.graph sourceMap3446=true := by decide +kernel
theorem fusedMap3446_checked : acceptsGraphIso
    (fused (graph core3446) (root 9) 0 5) DegreeTwoThreeSpectrum6246.graph fusedMap3446=true := by decide +kernel
theorem certified3446 : Certified (graph core3446) (root 9) 0 5 :=
  of_native_maps core3446 DegreeTwoThreeSpectrum6245.graph DegreeTwoThreeSpectrum6246.graph
    sourceMap3446 fusedMap3446 sourceMap3446_checked fusedMap3446_checked
    DegreeTwoThreeFiniteComparisons.comparison3446
#print axioms sourceMap3446_checked
#print axioms fusedMap3446_checked
#print axioms certified3446
def sourceMap3446swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3446swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3446swap_checked : acceptsGraphIso
    (source (graph core3446) (root 9) 5 0) DegreeTwoThreeSpectrum6245.graph sourceMap3446swap=true := by decide +kernel
theorem fusedMap3446swap_checked : acceptsGraphIso
    (fused (graph core3446) (root 9) 5 0) DegreeTwoThreeSpectrum6246.graph fusedMap3446swap=true := by decide +kernel
theorem certified3446swap : Certified (graph core3446) (root 9) 5 0 :=
  of_native_maps core3446 DegreeTwoThreeSpectrum6245.graph DegreeTwoThreeSpectrum6246.graph
    sourceMap3446swap fusedMap3446swap sourceMap3446swap_checked fusedMap3446swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3446
#print axioms sourceMap3446swap_checked
#print axioms fusedMap3446swap_checked
#print axioms certified3446swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
