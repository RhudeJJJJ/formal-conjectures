/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0356 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0356 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0356 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0356_checked : acceptsGraphIso
    (source (graph core0356) (root 6) 2 2) DegreeOneSmallSpectrum1385.graph sourceMap0356=true := by decide +kernel
theorem fusedMap0356_checked : acceptsGraphIso
    (fused (graph core0356) (root 6) 2 2) DegreeOneSmallSpectrum922.graph fusedMap0356=true := by decide +kernel
theorem certified0356 : Certified (graph core0356) (root 6) 2 2 :=
  of_native_maps core0356 DegreeOneSmallSpectrum1385.graph DegreeOneSmallSpectrum922.graph
    sourceMap0356 fusedMap0356 sourceMap0356_checked fusedMap0356_checked
    DegreeOneSmallComparisons.comparison0356
#print axioms sourceMap0356_checked
#print axioms fusedMap0356_checked
#print axioms certified0356
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
