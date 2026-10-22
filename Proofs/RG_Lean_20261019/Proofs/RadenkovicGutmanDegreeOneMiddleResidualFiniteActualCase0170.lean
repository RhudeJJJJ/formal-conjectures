/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0170 : Family 8 := level8.get ⟨230,by decide⟩
def sourceMap0170 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0170 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0170_checked : acceptsGraphIso
    (source (graph core0170) (root 8) 2 2) DegreeOneMiddleResidualSpectrum354.graph sourceMap0170=true := by decide +kernel
theorem fusedMap0170_checked : acceptsGraphIso
    (fused (graph core0170) (root 8) 2 2) DegreeOneMiddleResidualSpectrum208.graph fusedMap0170=true := by decide +kernel
theorem certified0170 : Certified (graph core0170) (root 8) 2 2 :=
  of_native_maps core0170 DegreeOneMiddleResidualSpectrum354.graph DegreeOneMiddleResidualSpectrum208.graph
    sourceMap0170 fusedMap0170 sourceMap0170_checked fusedMap0170_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0170
#print axioms sourceMap0170_checked
#print axioms fusedMap0170_checked
#print axioms certified0170
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
