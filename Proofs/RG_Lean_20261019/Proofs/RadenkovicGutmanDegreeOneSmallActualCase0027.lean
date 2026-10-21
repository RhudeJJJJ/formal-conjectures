/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0027 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0027 : (Vertices 1 ⊕ Fin 4 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,6,2,3,4,5,0,7,8,9,10,11,12] (sourceLabel 1 3 6 v)
def fusedMap0027 : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 3 6 v)
theorem sourceMap0027_checked : acceptsGraphIso
    (source (graph core0027) (root 1) 3 6) DegreeOneSmallSpectrum859.graph sourceMap0027=true := by decide +kernel
theorem fusedMap0027_checked : acceptsGraphIso
    (fused (graph core0027) (root 1) 3 6) DegreeOneSmallSpectrum861.graph fusedMap0027=true := by decide +kernel
theorem certified0027 : Certified (graph core0027) (root 1) 3 6 :=
  of_native_maps core0027 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0027 fusedMap0027 sourceMap0027_checked fusedMap0027_checked
    DegreeOneSmallComparisons.comparison0027
#print axioms sourceMap0027_checked
#print axioms fusedMap0027_checked
#print axioms certified0027
def sourceMap0027swap : (Vertices 1 ⊕ Fin 7 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,6,0,7,8,9,10,11,12,2,3,4,5] (sourceLabel 1 6 3 v)
def fusedMap0027swap : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 6 3 v)
theorem sourceMap0027swap_checked : acceptsGraphIso
    (source (graph core0027) (root 1) 6 3) DegreeOneSmallSpectrum859.graph sourceMap0027swap=true := by decide +kernel
theorem fusedMap0027swap_checked : acceptsGraphIso
    (fused (graph core0027) (root 1) 6 3) DegreeOneSmallSpectrum861.graph fusedMap0027swap=true := by decide +kernel
theorem certified0027swap : Certified (graph core0027) (root 1) 6 3 :=
  of_native_maps core0027 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0027swap fusedMap0027swap sourceMap0027swap_checked fusedMap0027swap_checked
    DegreeOneSmallComparisons.comparison0027
#print axioms sourceMap0027swap_checked
#print axioms fusedMap0027swap_checked
#print axioms certified0027swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
