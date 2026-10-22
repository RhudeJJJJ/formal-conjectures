/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3431 : Family 9 := level9.get ⟨570,by decide⟩
def sourceMap3431 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3431 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3431_checked : acceptsGraphIso
    (source (graph core3431) (root 9) 0 5) DegreeTwoThreeSpectrum6075.graph sourceMap3431=true := by decide +kernel
theorem fusedMap3431_checked : acceptsGraphIso
    (fused (graph core3431) (root 9) 0 5) DegreeTwoThreeSpectrum6076.graph fusedMap3431=true := by decide +kernel
theorem certified3431 : Certified (graph core3431) (root 9) 0 5 :=
  of_native_maps core3431 DegreeTwoThreeSpectrum6075.graph DegreeTwoThreeSpectrum6076.graph
    sourceMap3431 fusedMap3431 sourceMap3431_checked fusedMap3431_checked
    DegreeTwoThreeFiniteComparisons.comparison3431
#print axioms sourceMap3431_checked
#print axioms fusedMap3431_checked
#print axioms certified3431
def sourceMap3431swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3431swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3431swap_checked : acceptsGraphIso
    (source (graph core3431) (root 9) 5 0) DegreeTwoThreeSpectrum6075.graph sourceMap3431swap=true := by decide +kernel
theorem fusedMap3431swap_checked : acceptsGraphIso
    (fused (graph core3431) (root 9) 5 0) DegreeTwoThreeSpectrum6076.graph fusedMap3431swap=true := by decide +kernel
theorem certified3431swap : Certified (graph core3431) (root 9) 5 0 :=
  of_native_maps core3431 DegreeTwoThreeSpectrum6075.graph DegreeTwoThreeSpectrum6076.graph
    sourceMap3431swap fusedMap3431swap sourceMap3431swap_checked fusedMap3431swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3431
#print axioms sourceMap3431swap_checked
#print axioms fusedMap3431swap_checked
#print axioms certified3431swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
