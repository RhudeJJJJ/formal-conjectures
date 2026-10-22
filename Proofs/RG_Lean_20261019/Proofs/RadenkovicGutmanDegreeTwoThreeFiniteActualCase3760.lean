/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3760 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3760 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 1 2 v)
def fusedMap3760 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap3760_checked : acceptsGraphIso
    (source (graph core3760) (root 4) 1 2) DegreeOneSmallSpectrum130.graph sourceMap3760=true := by decide +kernel
theorem fusedMap3760_checked : acceptsGraphIso
    (fused (graph core3760) (root 4) 1 2) DegreeOneSmallSpectrum081.graph fusedMap3760=true := by decide +kernel
theorem certified3760 : Certified (graph core3760) (root 4) 1 2 :=
  of_native_maps core3760 DegreeOneSmallSpectrum130.graph DegreeOneSmallSpectrum081.graph
    sourceMap3760 fusedMap3760 sourceMap3760_checked fusedMap3760_checked
    DegreeTwoThreeFiniteComparisons.comparison3760
#print axioms sourceMap3760_checked
#print axioms fusedMap3760_checked
#print axioms certified3760
def sourceMap3760swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6] (sourceLabel 4 2 1 v)
def fusedMap3760swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap3760swap_checked : acceptsGraphIso
    (source (graph core3760) (root 4) 2 1) DegreeOneSmallSpectrum130.graph sourceMap3760swap=true := by decide +kernel
theorem fusedMap3760swap_checked : acceptsGraphIso
    (fused (graph core3760) (root 4) 2 1) DegreeOneSmallSpectrum081.graph fusedMap3760swap=true := by decide +kernel
theorem certified3760swap : Certified (graph core3760) (root 4) 2 1 :=
  of_native_maps core3760 DegreeOneSmallSpectrum130.graph DegreeOneSmallSpectrum081.graph
    sourceMap3760swap fusedMap3760swap sourceMap3760swap_checked fusedMap3760swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3760
#print axioms sourceMap3760swap_checked
#print axioms fusedMap3760swap_checked
#print axioms certified3760swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
