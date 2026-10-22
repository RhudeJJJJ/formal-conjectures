/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3045 : Family 10 := level10.get ⟨1680,by decide⟩
def sourceMap3045 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3045 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3045_checked : acceptsGraphIso
    (source (graph core3045) (root 10) 0 4) DegreeTwoThreeSpectrum7261.graph sourceMap3045=true := by decide +kernel
theorem fusedMap3045_checked : acceptsGraphIso
    (fused (graph core3045) (root 10) 0 4) DegreeTwoThreeSpectrum6341.graph fusedMap3045=true := by decide +kernel
theorem certified3045 : Certified (graph core3045) (root 10) 0 4 :=
  of_native_maps core3045 DegreeTwoThreeSpectrum7261.graph DegreeTwoThreeSpectrum6341.graph
    sourceMap3045 fusedMap3045 sourceMap3045_checked fusedMap3045_checked
    DegreeTwoThreeFiniteComparisons.comparison3045
#print axioms sourceMap3045_checked
#print axioms fusedMap3045_checked
#print axioms certified3045
def sourceMap3045swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3045swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3045swap_checked : acceptsGraphIso
    (source (graph core3045) (root 10) 4 0) DegreeTwoThreeSpectrum7261.graph sourceMap3045swap=true := by decide +kernel
theorem fusedMap3045swap_checked : acceptsGraphIso
    (fused (graph core3045) (root 10) 4 0) DegreeTwoThreeSpectrum6341.graph fusedMap3045swap=true := by decide +kernel
theorem certified3045swap : Certified (graph core3045) (root 10) 4 0 :=
  of_native_maps core3045 DegreeTwoThreeSpectrum7261.graph DegreeTwoThreeSpectrum6341.graph
    sourceMap3045swap fusedMap3045swap sourceMap3045swap_checked fusedMap3045swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3045
#print axioms sourceMap3045swap_checked
#print axioms fusedMap3045swap_checked
#print axioms certified3045swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
