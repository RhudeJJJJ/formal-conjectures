/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3498 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3498 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3498 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3498_checked : acceptsGraphIso
    (source (graph core3498) (root 6) 0 6) DegreeTwoThreeSpectrum2834.graph sourceMap3498=true := by decide +kernel
theorem fusedMap3498_checked : acceptsGraphIso
    (fused (graph core3498) (root 6) 0 6) DegreeTwoThreeSpectrum2382.graph fusedMap3498=true := by decide +kernel
theorem certified3498 : Certified (graph core3498) (root 6) 0 6 :=
  of_native_maps core3498 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap3498 fusedMap3498 sourceMap3498_checked fusedMap3498_checked
    DegreeTwoThreeFiniteComparisons.comparison3498
#print axioms sourceMap3498_checked
#print axioms fusedMap3498_checked
#print axioms certified3498
def sourceMap3498swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3498swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3498swap_checked : acceptsGraphIso
    (source (graph core3498) (root 6) 6 0) DegreeTwoThreeSpectrum2834.graph sourceMap3498swap=true := by decide +kernel
theorem fusedMap3498swap_checked : acceptsGraphIso
    (fused (graph core3498) (root 6) 6 0) DegreeTwoThreeSpectrum2382.graph fusedMap3498swap=true := by decide +kernel
theorem certified3498swap : Certified (graph core3498) (root 6) 6 0 :=
  of_native_maps core3498 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap3498swap fusedMap3498swap sourceMap3498swap_checked fusedMap3498swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3498
#print axioms sourceMap3498swap_checked
#print axioms fusedMap3498swap_checked
#print axioms certified3498swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
