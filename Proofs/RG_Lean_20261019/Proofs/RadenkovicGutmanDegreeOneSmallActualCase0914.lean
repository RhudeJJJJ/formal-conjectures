/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0914 : Family 8 := level8.get ⟨59,by decide⟩
def sourceMap0914 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0914 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0914_checked : acceptsGraphIso
    (source (graph core0914) (root 8) 1 1) DegreeOneSmallSpectrum1325.graph sourceMap0914=true := by decide +kernel
theorem fusedMap0914_checked : acceptsGraphIso
    (fused (graph core0914) (root 8) 1 1) DegreeOneSmallSpectrum918.graph fusedMap0914=true := by decide +kernel
theorem certified0914 : Certified (graph core0914) (root 8) 1 1 :=
  of_native_maps core0914 DegreeOneSmallSpectrum1325.graph DegreeOneSmallSpectrum918.graph
    sourceMap0914 fusedMap0914 sourceMap0914_checked fusedMap0914_checked
    DegreeOneSmallComparisons.comparison0914
#print axioms sourceMap0914_checked
#print axioms fusedMap0914_checked
#print axioms certified0914
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
