/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3442 : Family 9 := level9.get ⟨594,by decide⟩
def sourceMap3442 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3442 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3442_checked : acceptsGraphIso
    (source (graph core3442) (root 9) 0 5) DegreeTwoThreeSpectrum6204.graph sourceMap3442=true := by decide +kernel
theorem fusedMap3442_checked : acceptsGraphIso
    (fused (graph core3442) (root 9) 0 5) DegreeTwoThreeSpectrum6205.graph fusedMap3442=true := by decide +kernel
theorem certified3442 : Certified (graph core3442) (root 9) 0 5 :=
  of_native_maps core3442 DegreeTwoThreeSpectrum6204.graph DegreeTwoThreeSpectrum6205.graph
    sourceMap3442 fusedMap3442 sourceMap3442_checked fusedMap3442_checked
    DegreeTwoThreeFiniteComparisons.comparison3442
#print axioms sourceMap3442_checked
#print axioms fusedMap3442_checked
#print axioms certified3442
def sourceMap3442swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3442swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3442swap_checked : acceptsGraphIso
    (source (graph core3442) (root 9) 5 0) DegreeTwoThreeSpectrum6204.graph sourceMap3442swap=true := by decide +kernel
theorem fusedMap3442swap_checked : acceptsGraphIso
    (fused (graph core3442) (root 9) 5 0) DegreeTwoThreeSpectrum6205.graph fusedMap3442swap=true := by decide +kernel
theorem certified3442swap : Certified (graph core3442) (root 9) 5 0 :=
  of_native_maps core3442 DegreeTwoThreeSpectrum6204.graph DegreeTwoThreeSpectrum6205.graph
    sourceMap3442swap fusedMap3442swap sourceMap3442swap_checked fusedMap3442swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3442
#print axioms sourceMap3442swap_checked
#print axioms fusedMap3442swap_checked
#print axioms certified3442swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
