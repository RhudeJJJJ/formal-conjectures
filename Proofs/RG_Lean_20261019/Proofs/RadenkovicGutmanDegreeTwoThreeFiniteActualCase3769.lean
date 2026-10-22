/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3769 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3769 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3769 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3769_checked : acceptsGraphIso
    (source (graph core3769) (root 5) 1 4) DegreeOneSmallSpectrum1201.graph sourceMap3769=true := by decide +kernel
theorem fusedMap3769_checked : acceptsGraphIso
    (fused (graph core3769) (root 5) 1 4) DegreeOneSmallSpectrum887.graph fusedMap3769=true := by decide +kernel
theorem certified3769 : Certified (graph core3769) (root 5) 1 4 :=
  of_native_maps core3769 DegreeOneSmallSpectrum1201.graph DegreeOneSmallSpectrum887.graph
    sourceMap3769 fusedMap3769 sourceMap3769_checked fusedMap3769_checked
    DegreeTwoThreeFiniteComparisons.comparison3769
#print axioms sourceMap3769_checked
#print axioms fusedMap3769_checked
#print axioms certified3769
def sourceMap3769swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap3769swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3769swap_checked : acceptsGraphIso
    (source (graph core3769) (root 5) 4 1) DegreeOneSmallSpectrum1201.graph sourceMap3769swap=true := by decide +kernel
theorem fusedMap3769swap_checked : acceptsGraphIso
    (fused (graph core3769) (root 5) 4 1) DegreeOneSmallSpectrum887.graph fusedMap3769swap=true := by decide +kernel
theorem certified3769swap : Certified (graph core3769) (root 5) 4 1 :=
  of_native_maps core3769 DegreeOneSmallSpectrum1201.graph DegreeOneSmallSpectrum887.graph
    sourceMap3769swap fusedMap3769swap sourceMap3769swap_checked fusedMap3769swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3769
#print axioms sourceMap3769swap_checked
#print axioms fusedMap3769swap_checked
#print axioms certified3769swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
