/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3415 : Family 9 := level9.get ⟨527,by decide⟩
def sourceMap3415 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3415 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3415_checked : acceptsGraphIso
    (source (graph core3415) (root 9) 0 5) DegreeTwoThreeSpectrum6999.graph sourceMap3415=true := by decide +kernel
theorem fusedMap3415_checked : acceptsGraphIso
    (fused (graph core3415) (root 9) 0 5) DegreeTwoThreeSpectrum5821.graph fusedMap3415=true := by decide +kernel
theorem certified3415 : Certified (graph core3415) (root 9) 0 5 :=
  of_native_maps core3415 DegreeTwoThreeSpectrum6999.graph DegreeTwoThreeSpectrum5821.graph
    sourceMap3415 fusedMap3415 sourceMap3415_checked fusedMap3415_checked
    DegreeTwoThreeFiniteComparisons.comparison3415
#print axioms sourceMap3415_checked
#print axioms fusedMap3415_checked
#print axioms certified3415
def sourceMap3415swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3415swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3415swap_checked : acceptsGraphIso
    (source (graph core3415) (root 9) 5 0) DegreeTwoThreeSpectrum6999.graph sourceMap3415swap=true := by decide +kernel
theorem fusedMap3415swap_checked : acceptsGraphIso
    (fused (graph core3415) (root 9) 5 0) DegreeTwoThreeSpectrum5821.graph fusedMap3415swap=true := by decide +kernel
theorem certified3415swap : Certified (graph core3415) (root 9) 5 0 :=
  of_native_maps core3415 DegreeTwoThreeSpectrum6999.graph DegreeTwoThreeSpectrum5821.graph
    sourceMap3415swap fusedMap3415swap sourceMap3415swap_checked fusedMap3415swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3415
#print axioms sourceMap3415swap_checked
#print axioms fusedMap3415swap_checked
#print axioms certified3415swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
