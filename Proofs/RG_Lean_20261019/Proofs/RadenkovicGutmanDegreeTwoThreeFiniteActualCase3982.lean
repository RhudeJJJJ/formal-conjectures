/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3982 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap3982 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3982 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3982_checked : acceptsGraphIso
    (source (graph core3982) (root 7) 1 5) DegreeTwoThreeSpectrum4490.graph sourceMap3982=true := by decide +kernel
theorem fusedMap3982_checked : acceptsGraphIso
    (fused (graph core3982) (root 7) 1 5) DegreeTwoThreeSpectrum4019.graph fusedMap3982=true := by decide +kernel
theorem certified3982 : Certified (graph core3982) (root 7) 1 5 :=
  of_native_maps core3982 DegreeTwoThreeSpectrum4490.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap3982 fusedMap3982 sourceMap3982_checked fusedMap3982_checked
    DegreeTwoThreeFiniteComparisons.comparison3982
#print axioms sourceMap3982_checked
#print axioms fusedMap3982_checked
#print axioms certified3982
def sourceMap3982swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3982swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3982swap_checked : acceptsGraphIso
    (source (graph core3982) (root 7) 5 1) DegreeTwoThreeSpectrum4490.graph sourceMap3982swap=true := by decide +kernel
theorem fusedMap3982swap_checked : acceptsGraphIso
    (fused (graph core3982) (root 7) 5 1) DegreeTwoThreeSpectrum4019.graph fusedMap3982swap=true := by decide +kernel
theorem certified3982swap : Certified (graph core3982) (root 7) 5 1 :=
  of_native_maps core3982 DegreeTwoThreeSpectrum4490.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap3982swap fusedMap3982swap sourceMap3982swap_checked fusedMap3982swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3982
#print axioms sourceMap3982swap_checked
#print axioms fusedMap3982swap_checked
#print axioms certified3982swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
