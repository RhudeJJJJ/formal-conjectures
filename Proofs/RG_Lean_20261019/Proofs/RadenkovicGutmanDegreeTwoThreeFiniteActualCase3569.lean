/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3569 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap3569 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3569 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3569_checked : acceptsGraphIso
    (source (graph core3569) (root 8) 0 6) DegreeTwoThreeSpectrum5239.graph sourceMap3569=true := by decide +kernel
theorem fusedMap3569_checked : acceptsGraphIso
    (fused (graph core3569) (root 8) 0 6) DegreeTwoThreeSpectrum5241.graph fusedMap3569=true := by decide +kernel
theorem certified3569 : Certified (graph core3569) (root 8) 0 6 :=
  of_native_maps core3569 DegreeTwoThreeSpectrum5239.graph DegreeTwoThreeSpectrum5241.graph
    sourceMap3569 fusedMap3569 sourceMap3569_checked fusedMap3569_checked
    DegreeTwoThreeFiniteComparisons.comparison3569
#print axioms sourceMap3569_checked
#print axioms fusedMap3569_checked
#print axioms certified3569
def sourceMap3569swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3569swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3569swap_checked : acceptsGraphIso
    (source (graph core3569) (root 8) 6 0) DegreeTwoThreeSpectrum5239.graph sourceMap3569swap=true := by decide +kernel
theorem fusedMap3569swap_checked : acceptsGraphIso
    (fused (graph core3569) (root 8) 6 0) DegreeTwoThreeSpectrum5241.graph fusedMap3569swap=true := by decide +kernel
theorem certified3569swap : Certified (graph core3569) (root 8) 6 0 :=
  of_native_maps core3569 DegreeTwoThreeSpectrum5239.graph DegreeTwoThreeSpectrum5241.graph
    sourceMap3569swap fusedMap3569swap sourceMap3569swap_checked fusedMap3569swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3569
#print axioms sourceMap3569swap_checked
#print axioms fusedMap3569swap_checked
#print axioms certified3569swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
