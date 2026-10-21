/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0388 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0388 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0388 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0388_checked : acceptsGraphIso
    (source (graph core0388) (root 6) 0 4) DegreeOneSmallSpectrum998.graph sourceMap0388=true := by decide +kernel
theorem fusedMap0388_checked : acceptsGraphIso
    (fused (graph core0388) (root 6) 0 4) DegreeOneSmallSpectrum862.graph fusedMap0388=true := by decide +kernel
theorem certified0388 : Certified (graph core0388) (root 6) 0 4 :=
  of_native_maps core0388 DegreeOneSmallSpectrum998.graph DegreeOneSmallSpectrum862.graph
    sourceMap0388 fusedMap0388 sourceMap0388_checked fusedMap0388_checked
    DegreeOneSmallComparisons.comparison0388
#print axioms sourceMap0388_checked
#print axioms fusedMap0388_checked
#print axioms certified0388
def sourceMap0388swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0388swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0388swap_checked : acceptsGraphIso
    (source (graph core0388) (root 6) 4 0) DegreeOneSmallSpectrum998.graph sourceMap0388swap=true := by decide +kernel
theorem fusedMap0388swap_checked : acceptsGraphIso
    (fused (graph core0388) (root 6) 4 0) DegreeOneSmallSpectrum862.graph fusedMap0388swap=true := by decide +kernel
theorem certified0388swap : Certified (graph core0388) (root 6) 4 0 :=
  of_native_maps core0388 DegreeOneSmallSpectrum998.graph DegreeOneSmallSpectrum862.graph
    sourceMap0388swap fusedMap0388swap sourceMap0388swap_checked fusedMap0388swap_checked
    DegreeOneSmallComparisons.comparison0388
#print axioms sourceMap0388swap_checked
#print axioms fusedMap0388swap_checked
#print axioms certified0388swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
