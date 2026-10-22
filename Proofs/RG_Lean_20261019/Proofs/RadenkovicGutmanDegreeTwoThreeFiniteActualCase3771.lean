/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3771 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3771 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3771 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3771_checked : acceptsGraphIso
    (source (graph core3771) (root 5) 1 4) DegreeOneSmallSpectrum1478.graph sourceMap3771=true := by decide +kernel
theorem fusedMap3771_checked : acceptsGraphIso
    (fused (graph core3771) (root 5) 1 4) DegreeOneSmallSpectrum951.graph fusedMap3771=true := by decide +kernel
theorem certified3771 : Certified (graph core3771) (root 5) 1 4 :=
  of_native_maps core3771 DegreeOneSmallSpectrum1478.graph DegreeOneSmallSpectrum951.graph
    sourceMap3771 fusedMap3771 sourceMap3771_checked fusedMap3771_checked
    DegreeTwoThreeFiniteComparisons.comparison3771
#print axioms sourceMap3771_checked
#print axioms fusedMap3771_checked
#print axioms certified3771
def sourceMap3771swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap3771swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3771swap_checked : acceptsGraphIso
    (source (graph core3771) (root 5) 4 1) DegreeOneSmallSpectrum1478.graph sourceMap3771swap=true := by decide +kernel
theorem fusedMap3771swap_checked : acceptsGraphIso
    (fused (graph core3771) (root 5) 4 1) DegreeOneSmallSpectrum951.graph fusedMap3771swap=true := by decide +kernel
theorem certified3771swap : Certified (graph core3771) (root 5) 4 1 :=
  of_native_maps core3771 DegreeOneSmallSpectrum1478.graph DegreeOneSmallSpectrum951.graph
    sourceMap3771swap fusedMap3771swap sourceMap3771swap_checked fusedMap3771swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3771
#print axioms sourceMap3771swap_checked
#print axioms fusedMap3771swap_checked
#print axioms certified3771swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
