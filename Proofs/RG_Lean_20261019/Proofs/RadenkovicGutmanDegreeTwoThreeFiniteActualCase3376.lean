/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3376 : Family 9 := level9.get ⟨435,by decide⟩
def sourceMap3376 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3376 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3376_checked : acceptsGraphIso
    (source (graph core3376) (root 9) 0 5) DegreeTwoThreeSpectrum6570.graph sourceMap3376=true := by decide +kernel
theorem fusedMap3376_checked : acceptsGraphIso
    (fused (graph core3376) (root 9) 0 5) DegreeTwoThreeSpectrum5460.graph fusedMap3376=true := by decide +kernel
theorem certified3376 : Certified (graph core3376) (root 9) 0 5 :=
  of_native_maps core3376 DegreeTwoThreeSpectrum6570.graph DegreeTwoThreeSpectrum5460.graph
    sourceMap3376 fusedMap3376 sourceMap3376_checked fusedMap3376_checked
    DegreeTwoThreeFiniteComparisons.comparison3376
#print axioms sourceMap3376_checked
#print axioms fusedMap3376_checked
#print axioms certified3376
def sourceMap3376swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3376swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3376swap_checked : acceptsGraphIso
    (source (graph core3376) (root 9) 5 0) DegreeTwoThreeSpectrum6570.graph sourceMap3376swap=true := by decide +kernel
theorem fusedMap3376swap_checked : acceptsGraphIso
    (fused (graph core3376) (root 9) 5 0) DegreeTwoThreeSpectrum5460.graph fusedMap3376swap=true := by decide +kernel
theorem certified3376swap : Certified (graph core3376) (root 9) 5 0 :=
  of_native_maps core3376 DegreeTwoThreeSpectrum6570.graph DegreeTwoThreeSpectrum5460.graph
    sourceMap3376swap fusedMap3376swap sourceMap3376swap_checked fusedMap3376swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3376
#print axioms sourceMap3376swap_checked
#print axioms fusedMap3376swap_checked
#print axioms certified3376swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
