/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3447 : Family 9 := level9.get ⟨604,by decide⟩
def sourceMap3447 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3447 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3447_checked : acceptsGraphIso
    (source (graph core3447) (root 9) 0 5) DegreeTwoThreeSpectrum6256.graph sourceMap3447=true := by decide +kernel
theorem fusedMap3447_checked : acceptsGraphIso
    (fused (graph core3447) (root 9) 0 5) DegreeTwoThreeSpectrum6257.graph fusedMap3447=true := by decide +kernel
theorem certified3447 : Certified (graph core3447) (root 9) 0 5 :=
  of_native_maps core3447 DegreeTwoThreeSpectrum6256.graph DegreeTwoThreeSpectrum6257.graph
    sourceMap3447 fusedMap3447 sourceMap3447_checked fusedMap3447_checked
    DegreeTwoThreeFiniteComparisons.comparison3447
#print axioms sourceMap3447_checked
#print axioms fusedMap3447_checked
#print axioms certified3447
def sourceMap3447swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3447swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3447swap_checked : acceptsGraphIso
    (source (graph core3447) (root 9) 5 0) DegreeTwoThreeSpectrum6256.graph sourceMap3447swap=true := by decide +kernel
theorem fusedMap3447swap_checked : acceptsGraphIso
    (fused (graph core3447) (root 9) 5 0) DegreeTwoThreeSpectrum6257.graph fusedMap3447swap=true := by decide +kernel
theorem certified3447swap : Certified (graph core3447) (root 9) 5 0 :=
  of_native_maps core3447 DegreeTwoThreeSpectrum6256.graph DegreeTwoThreeSpectrum6257.graph
    sourceMap3447swap fusedMap3447swap sourceMap3447swap_checked fusedMap3447swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3447
#print axioms sourceMap3447swap_checked
#print axioms fusedMap3447swap_checked
#print axioms certified3447swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
