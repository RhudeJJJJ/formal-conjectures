/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3435 : Family 9 := level9.get ⟨577,by decide⟩
def sourceMap3435 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3435 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3435_checked : acceptsGraphIso
    (source (graph core3435) (root 9) 0 5) DegreeTwoThreeSpectrum6116.graph sourceMap3435=true := by decide +kernel
theorem fusedMap3435_checked : acceptsGraphIso
    (fused (graph core3435) (root 9) 0 5) DegreeTwoThreeSpectrum6117.graph fusedMap3435=true := by decide +kernel
theorem certified3435 : Certified (graph core3435) (root 9) 0 5 :=
  of_native_maps core3435 DegreeTwoThreeSpectrum6116.graph DegreeTwoThreeSpectrum6117.graph
    sourceMap3435 fusedMap3435 sourceMap3435_checked fusedMap3435_checked
    DegreeTwoThreeFiniteComparisons.comparison3435
#print axioms sourceMap3435_checked
#print axioms fusedMap3435_checked
#print axioms certified3435
def sourceMap3435swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3435swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3435swap_checked : acceptsGraphIso
    (source (graph core3435) (root 9) 5 0) DegreeTwoThreeSpectrum6116.graph sourceMap3435swap=true := by decide +kernel
theorem fusedMap3435swap_checked : acceptsGraphIso
    (fused (graph core3435) (root 9) 5 0) DegreeTwoThreeSpectrum6117.graph fusedMap3435swap=true := by decide +kernel
theorem certified3435swap : Certified (graph core3435) (root 9) 5 0 :=
  of_native_maps core3435 DegreeTwoThreeSpectrum6116.graph DegreeTwoThreeSpectrum6117.graph
    sourceMap3435swap fusedMap3435swap sourceMap3435swap_checked fusedMap3435swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3435
#print axioms sourceMap3435swap_checked
#print axioms fusedMap3435swap_checked
#print axioms certified3435swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
