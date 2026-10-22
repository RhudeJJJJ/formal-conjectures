/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3441 : Family 9 := level9.get ⟨593,by decide⟩
def sourceMap3441 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3441 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3441_checked : acceptsGraphIso
    (source (graph core3441) (root 9) 0 5) DegreeTwoThreeSpectrum6198.graph sourceMap3441=true := by decide +kernel
theorem fusedMap3441_checked : acceptsGraphIso
    (fused (graph core3441) (root 9) 0 5) DegreeTwoThreeSpectrum6199.graph fusedMap3441=true := by decide +kernel
theorem certified3441 : Certified (graph core3441) (root 9) 0 5 :=
  of_native_maps core3441 DegreeTwoThreeSpectrum6198.graph DegreeTwoThreeSpectrum6199.graph
    sourceMap3441 fusedMap3441 sourceMap3441_checked fusedMap3441_checked
    DegreeTwoThreeFiniteComparisons.comparison3441
#print axioms sourceMap3441_checked
#print axioms fusedMap3441_checked
#print axioms certified3441
def sourceMap3441swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3441swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3441swap_checked : acceptsGraphIso
    (source (graph core3441) (root 9) 5 0) DegreeTwoThreeSpectrum6198.graph sourceMap3441swap=true := by decide +kernel
theorem fusedMap3441swap_checked : acceptsGraphIso
    (fused (graph core3441) (root 9) 5 0) DegreeTwoThreeSpectrum6199.graph fusedMap3441swap=true := by decide +kernel
theorem certified3441swap : Certified (graph core3441) (root 9) 5 0 :=
  of_native_maps core3441 DegreeTwoThreeSpectrum6198.graph DegreeTwoThreeSpectrum6199.graph
    sourceMap3441swap fusedMap3441swap sourceMap3441swap_checked fusedMap3441swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3441
#print axioms sourceMap3441swap_checked
#print axioms fusedMap3441swap_checked
#print axioms certified3441swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
