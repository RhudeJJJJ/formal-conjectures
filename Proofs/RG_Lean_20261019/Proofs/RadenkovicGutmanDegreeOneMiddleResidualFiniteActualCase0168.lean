/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0168 : Family 8 := level8.get ⟨210,by decide⟩
def sourceMap0168 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0168 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0168_checked : acceptsGraphIso
    (source (graph core0168) (root 8) 2 2) DegreeOneMiddleResidualSpectrum352.graph sourceMap0168=true := by decide +kernel
theorem fusedMap0168_checked : acceptsGraphIso
    (fused (graph core0168) (root 8) 2 2) DegreeOneMiddleResidualSpectrum188.graph fusedMap0168=true := by decide +kernel
theorem certified0168 : Certified (graph core0168) (root 8) 2 2 :=
  of_native_maps core0168 DegreeOneMiddleResidualSpectrum352.graph DegreeOneMiddleResidualSpectrum188.graph
    sourceMap0168 fusedMap0168 sourceMap0168_checked fusedMap0168_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0168
#print axioms sourceMap0168_checked
#print axioms fusedMap0168_checked
#print axioms certified0168
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
