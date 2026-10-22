/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3120 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap3120 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3120 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3120_checked : acceptsGraphIso
    (source (graph core3120) (root 7) 0 5) DegreeTwoThreeSpectrum2956.graph sourceMap3120=true := by decide +kernel
theorem fusedMap3120_checked : acceptsGraphIso
    (fused (graph core3120) (root 7) 0 5) DegreeTwoThreeSpectrum2408.graph fusedMap3120=true := by decide +kernel
theorem certified3120 : Certified (graph core3120) (root 7) 0 5 :=
  of_native_maps core3120 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap3120 fusedMap3120 sourceMap3120_checked fusedMap3120_checked
    DegreeTwoThreeFiniteComparisons.comparison3120
#print axioms sourceMap3120_checked
#print axioms fusedMap3120_checked
#print axioms certified3120
def sourceMap3120swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3120swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3120swap_checked : acceptsGraphIso
    (source (graph core3120) (root 7) 5 0) DegreeTwoThreeSpectrum2956.graph sourceMap3120swap=true := by decide +kernel
theorem fusedMap3120swap_checked : acceptsGraphIso
    (fused (graph core3120) (root 7) 5 0) DegreeTwoThreeSpectrum2408.graph fusedMap3120swap=true := by decide +kernel
theorem certified3120swap : Certified (graph core3120) (root 7) 5 0 :=
  of_native_maps core3120 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2408.graph
    sourceMap3120swap fusedMap3120swap sourceMap3120swap_checked fusedMap3120swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3120
#print axioms sourceMap3120swap_checked
#print axioms fusedMap3120swap_checked
#print axioms certified3120swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
