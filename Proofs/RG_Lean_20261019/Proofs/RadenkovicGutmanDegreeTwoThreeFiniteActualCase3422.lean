/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3422 : Family 9 := level9.get ⟨548,by decide⟩
def sourceMap3422 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3422 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3422_checked : acceptsGraphIso
    (source (graph core3422) (root 9) 0 5) DegreeTwoThreeSpectrum5984.graph sourceMap3422=true := by decide +kernel
theorem fusedMap3422_checked : acceptsGraphIso
    (fused (graph core3422) (root 9) 0 5) DegreeTwoThreeSpectrum5985.graph fusedMap3422=true := by decide +kernel
theorem certified3422 : Certified (graph core3422) (root 9) 0 5 :=
  of_native_maps core3422 DegreeTwoThreeSpectrum5984.graph DegreeTwoThreeSpectrum5985.graph
    sourceMap3422 fusedMap3422 sourceMap3422_checked fusedMap3422_checked
    DegreeTwoThreeFiniteComparisons.comparison3422
#print axioms sourceMap3422_checked
#print axioms fusedMap3422_checked
#print axioms certified3422
def sourceMap3422swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3422swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3422swap_checked : acceptsGraphIso
    (source (graph core3422) (root 9) 5 0) DegreeTwoThreeSpectrum5984.graph sourceMap3422swap=true := by decide +kernel
theorem fusedMap3422swap_checked : acceptsGraphIso
    (fused (graph core3422) (root 9) 5 0) DegreeTwoThreeSpectrum5985.graph fusedMap3422swap=true := by decide +kernel
theorem certified3422swap : Certified (graph core3422) (root 9) 5 0 :=
  of_native_maps core3422 DegreeTwoThreeSpectrum5984.graph DegreeTwoThreeSpectrum5985.graph
    sourceMap3422swap fusedMap3422swap sourceMap3422swap_checked fusedMap3422swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3422
#print axioms sourceMap3422swap_checked
#print axioms fusedMap3422swap_checked
#print axioms certified3422swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
