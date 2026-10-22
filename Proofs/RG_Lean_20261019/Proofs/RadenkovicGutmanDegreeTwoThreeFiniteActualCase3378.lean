/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3378 : Family 9 := level9.get ⟨443,by decide⟩
def sourceMap3378 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3378 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3378_checked : acceptsGraphIso
    (source (graph core3378) (root 9) 0 5) DegreeTwoThreeSpectrum6610.graph sourceMap3378=true := by decide +kernel
theorem fusedMap3378_checked : acceptsGraphIso
    (fused (graph core3378) (root 9) 0 5) DegreeTwoThreeSpectrum5487.graph fusedMap3378=true := by decide +kernel
theorem certified3378 : Certified (graph core3378) (root 9) 0 5 :=
  of_native_maps core3378 DegreeTwoThreeSpectrum6610.graph DegreeTwoThreeSpectrum5487.graph
    sourceMap3378 fusedMap3378 sourceMap3378_checked fusedMap3378_checked
    DegreeTwoThreeFiniteComparisons.comparison3378
#print axioms sourceMap3378_checked
#print axioms fusedMap3378_checked
#print axioms certified3378
def sourceMap3378swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3378swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3378swap_checked : acceptsGraphIso
    (source (graph core3378) (root 9) 5 0) DegreeTwoThreeSpectrum6610.graph sourceMap3378swap=true := by decide +kernel
theorem fusedMap3378swap_checked : acceptsGraphIso
    (fused (graph core3378) (root 9) 5 0) DegreeTwoThreeSpectrum5487.graph fusedMap3378swap=true := by decide +kernel
theorem certified3378swap : Certified (graph core3378) (root 9) 5 0 :=
  of_native_maps core3378 DegreeTwoThreeSpectrum6610.graph DegreeTwoThreeSpectrum5487.graph
    sourceMap3378swap fusedMap3378swap sourceMap3378swap_checked fusedMap3378swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3378
#print axioms sourceMap3378swap_checked
#print axioms fusedMap3378swap_checked
#print axioms certified3378swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
