/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3525 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap3525 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3525 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3525_checked : acceptsGraphIso
    (source (graph core3525) (root 7) 0 6) DegreeTwoThreeSpectrum4296.graph sourceMap3525=true := by decide +kernel
theorem fusedMap3525_checked : acceptsGraphIso
    (fused (graph core3525) (root 7) 0 6) DegreeTwoThreeSpectrum3923.graph fusedMap3525=true := by decide +kernel
theorem certified3525 : Certified (graph core3525) (root 7) 0 6 :=
  of_native_maps core3525 DegreeTwoThreeSpectrum4296.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap3525 fusedMap3525 sourceMap3525_checked fusedMap3525_checked
    DegreeTwoThreeFiniteComparisons.comparison3525
#print axioms sourceMap3525_checked
#print axioms fusedMap3525_checked
#print axioms certified3525
def sourceMap3525swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3525swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3525swap_checked : acceptsGraphIso
    (source (graph core3525) (root 7) 6 0) DegreeTwoThreeSpectrum4296.graph sourceMap3525swap=true := by decide +kernel
theorem fusedMap3525swap_checked : acceptsGraphIso
    (fused (graph core3525) (root 7) 6 0) DegreeTwoThreeSpectrum3923.graph fusedMap3525swap=true := by decide +kernel
theorem certified3525swap : Certified (graph core3525) (root 7) 6 0 :=
  of_native_maps core3525 DegreeTwoThreeSpectrum4296.graph DegreeTwoThreeSpectrum3923.graph
    sourceMap3525swap fusedMap3525swap sourceMap3525swap_checked fusedMap3525swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3525
#print axioms sourceMap3525swap_checked
#print axioms fusedMap3525swap_checked
#print axioms certified3525swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
