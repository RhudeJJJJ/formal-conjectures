/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0302 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0302 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 6 2 2 v)
def fusedMap0302 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0302_checked : acceptsGraphIso
    (source (graph core0302) (root 6) 2 2) DegreeOneSmallSpectrum1462.graph sourceMap0302=true := by decide +kernel
theorem fusedMap0302_checked : acceptsGraphIso
    (fused (graph core0302) (root 6) 2 2) DegreeOneSmallSpectrum858.graph fusedMap0302=true := by decide +kernel
theorem certified0302 : Certified (graph core0302) (root 6) 2 2 :=
  of_native_maps core0302 DegreeOneSmallSpectrum1462.graph DegreeOneSmallSpectrum858.graph
    sourceMap0302 fusedMap0302 sourceMap0302_checked fusedMap0302_checked
    DegreeOneSmallComparisons.comparison0302
#print axioms sourceMap0302_checked
#print axioms fusedMap0302_checked
#print axioms certified0302
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
