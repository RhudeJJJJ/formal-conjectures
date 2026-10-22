/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3395 : Family 9 := level9.get ⟨479,by decide⟩
def sourceMap3395 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3395 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3395_checked : acceptsGraphIso
    (source (graph core3395) (root 9) 0 5) DegreeTwoThreeSpectrum6761.graph sourceMap3395=true := by decide +kernel
theorem fusedMap3395_checked : acceptsGraphIso
    (fused (graph core3395) (root 9) 0 5) DegreeTwoThreeSpectrum5598.graph fusedMap3395=true := by decide +kernel
theorem certified3395 : Certified (graph core3395) (root 9) 0 5 :=
  of_native_maps core3395 DegreeTwoThreeSpectrum6761.graph DegreeTwoThreeSpectrum5598.graph
    sourceMap3395 fusedMap3395 sourceMap3395_checked fusedMap3395_checked
    DegreeTwoThreeFiniteComparisons.comparison3395
#print axioms sourceMap3395_checked
#print axioms fusedMap3395_checked
#print axioms certified3395
def sourceMap3395swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3395swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3395swap_checked : acceptsGraphIso
    (source (graph core3395) (root 9) 5 0) DegreeTwoThreeSpectrum6761.graph sourceMap3395swap=true := by decide +kernel
theorem fusedMap3395swap_checked : acceptsGraphIso
    (fused (graph core3395) (root 9) 5 0) DegreeTwoThreeSpectrum5598.graph fusedMap3395swap=true := by decide +kernel
theorem certified3395swap : Certified (graph core3395) (root 9) 5 0 :=
  of_native_maps core3395 DegreeTwoThreeSpectrum6761.graph DegreeTwoThreeSpectrum5598.graph
    sourceMap3395swap fusedMap3395swap sourceMap3395swap_checked fusedMap3395swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3395
#print axioms sourceMap3395swap_checked
#print axioms fusedMap3395swap_checked
#print axioms certified3395swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
