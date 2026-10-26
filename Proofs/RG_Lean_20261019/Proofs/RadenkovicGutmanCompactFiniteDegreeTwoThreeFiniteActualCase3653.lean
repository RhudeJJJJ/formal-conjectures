/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3653 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3653 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3653 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3653_checked : acceptsGraphIso
    (source (graph core3653) (root 6) 0 7) DegreeTwoThreeSpectrum3943.graph sourceMap3653=true := by decide +kernel
theorem fusedMap3653_checked : acceptsGraphIso
    (fused (graph core3653) (root 6) 0 7) DegreeTwoThreeSpectrum3946.graph fusedMap3653=true := by decide +kernel
theorem certified3653 : Certified (graph core3653) (root 6) 0 7 :=
  of_native_maps core3653 DegreeTwoThreeSpectrum3943.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap3653 fusedMap3653 sourceMap3653_checked fusedMap3653_checked
    DegreeTwoThreeFiniteComparisons.comparison3653
#print axioms sourceMap3653_checked
#print axioms fusedMap3653_checked
#print axioms certified3653
def sourceMap3653swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3653swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3653swap_checked : acceptsGraphIso
    (source (graph core3653) (root 6) 7 0) DegreeTwoThreeSpectrum3943.graph sourceMap3653swap=true := by decide +kernel
theorem fusedMap3653swap_checked : acceptsGraphIso
    (fused (graph core3653) (root 6) 7 0) DegreeTwoThreeSpectrum3946.graph fusedMap3653swap=true := by decide +kernel
theorem certified3653swap : Certified (graph core3653) (root 6) 7 0 :=
  of_native_maps core3653 DegreeTwoThreeSpectrum3943.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap3653swap fusedMap3653swap sourceMap3653swap_checked fusedMap3653swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3653
#print axioms sourceMap3653swap_checked
#print axioms fusedMap3653swap_checked
#print axioms certified3653swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
