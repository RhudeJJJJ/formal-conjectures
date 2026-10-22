/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3733 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3733 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3733 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3733_checked : acceptsGraphIso
    (source (graph core3733) (root 5) 0 9) DegreeTwoThreeSpectrum5022.graph sourceMap3733=true := by decide +kernel
theorem fusedMap3733_checked : acceptsGraphIso
    (fused (graph core3733) (root 5) 0 9) DegreeTwoThreeSpectrum5027.graph fusedMap3733=true := by decide +kernel
theorem certified3733 : Certified (graph core3733) (root 5) 0 9 :=
  of_native_maps core3733 DegreeTwoThreeSpectrum5022.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap3733 fusedMap3733 sourceMap3733_checked fusedMap3733_checked
    DegreeTwoThreeFiniteComparisons.comparison3733
#print axioms sourceMap3733_checked
#print axioms fusedMap3733_checked
#print axioms certified3733
def sourceMap3733swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 5 9 0 v)
def fusedMap3733swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3733swap_checked : acceptsGraphIso
    (source (graph core3733) (root 5) 9 0) DegreeTwoThreeSpectrum5022.graph sourceMap3733swap=true := by decide +kernel
theorem fusedMap3733swap_checked : acceptsGraphIso
    (fused (graph core3733) (root 5) 9 0) DegreeTwoThreeSpectrum5027.graph fusedMap3733swap=true := by decide +kernel
theorem certified3733swap : Certified (graph core3733) (root 5) 9 0 :=
  of_native_maps core3733 DegreeTwoThreeSpectrum5022.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap3733swap fusedMap3733swap sourceMap3733swap_checked fusedMap3733swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3733
#print axioms sourceMap3733swap_checked
#print axioms fusedMap3733swap_checked
#print axioms certified3733swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
