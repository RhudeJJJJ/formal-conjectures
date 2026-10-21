/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0029 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0029 : (Vertices 1 ⊕ Fin 5 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,6,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 1 4 5 v)
def fusedMap0029 : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 4 5 v)
theorem sourceMap0029_checked : acceptsGraphIso
    (source (graph core0029) (root 1) 4 5) DegreeOneSmallSpectrum860.graph sourceMap0029=true := by decide +kernel
theorem fusedMap0029_checked : acceptsGraphIso
    (fused (graph core0029) (root 1) 4 5) DegreeOneSmallSpectrum861.graph fusedMap0029=true := by decide +kernel
theorem certified0029 : Certified (graph core0029) (root 1) 4 5 :=
  of_native_maps core0029 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0029 fusedMap0029 sourceMap0029_checked fusedMap0029_checked
    DegreeOneSmallComparisons.comparison0029
#print axioms sourceMap0029_checked
#print axioms fusedMap0029_checked
#print axioms certified0029
def sourceMap0029swap : (Vertices 1 ⊕ Fin 6 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (sourceLabel 1 5 4 v)
def fusedMap0029swap : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 5 4 v)
theorem sourceMap0029swap_checked : acceptsGraphIso
    (source (graph core0029) (root 1) 5 4) DegreeOneSmallSpectrum860.graph sourceMap0029swap=true := by decide +kernel
theorem fusedMap0029swap_checked : acceptsGraphIso
    (fused (graph core0029) (root 1) 5 4) DegreeOneSmallSpectrum861.graph fusedMap0029swap=true := by decide +kernel
theorem certified0029swap : Certified (graph core0029) (root 1) 5 4 :=
  of_native_maps core0029 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0029swap fusedMap0029swap sourceMap0029swap_checked fusedMap0029swap_checked
    DegreeOneSmallComparisons.comparison0029
#print axioms sourceMap0029swap_checked
#print axioms fusedMap0029swap_checked
#print axioms certified0029swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
