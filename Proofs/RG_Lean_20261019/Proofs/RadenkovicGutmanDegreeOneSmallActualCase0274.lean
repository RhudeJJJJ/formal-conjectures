/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0274 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0274 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 6 1 3 v)
def fusedMap0274 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0274_checked : acceptsGraphIso
    (source (graph core0274) (root 6) 1 3) DegreeOneSmallSpectrum971.graph sourceMap0274=true := by decide +kernel
theorem fusedMap0274_checked : acceptsGraphIso
    (fused (graph core0274) (root 6) 1 3) DegreeOneSmallSpectrum861.graph fusedMap0274=true := by decide +kernel
theorem certified0274 : Certified (graph core0274) (root 6) 1 3 :=
  of_native_maps core0274 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0274 fusedMap0274 sourceMap0274_checked fusedMap0274_checked
    DegreeOneSmallComparisons.comparison0274
#print axioms sourceMap0274_checked
#print axioms fusedMap0274_checked
#print axioms certified0274
def sourceMap0274swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 6 3 1 v)
def fusedMap0274swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0274swap_checked : acceptsGraphIso
    (source (graph core0274) (root 6) 3 1) DegreeOneSmallSpectrum971.graph sourceMap0274swap=true := by decide +kernel
theorem fusedMap0274swap_checked : acceptsGraphIso
    (fused (graph core0274) (root 6) 3 1) DegreeOneSmallSpectrum861.graph fusedMap0274swap=true := by decide +kernel
theorem certified0274swap : Certified (graph core0274) (root 6) 3 1 :=
  of_native_maps core0274 DegreeOneSmallSpectrum971.graph DegreeOneSmallSpectrum861.graph
    sourceMap0274swap fusedMap0274swap sourceMap0274swap_checked fusedMap0274swap_checked
    DegreeOneSmallComparisons.comparison0274
#print axioms sourceMap0274swap_checked
#print axioms fusedMap0274swap_checked
#print axioms certified0274swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
