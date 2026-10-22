/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0141 : Family 8 := level8.get ⟨133,by decide⟩
def sourceMap0141 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0141 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0141_checked : acceptsGraphIso
    (source (graph core0141) (root 8) 2 2) DegreeOneMiddleResidualSpectrum299.graph sourceMap0141=true := by decide +kernel
theorem fusedMap0141_checked : acceptsGraphIso
    (fused (graph core0141) (root 8) 2 2) DegreeOneMiddleResidualSpectrum211.graph fusedMap0141=true := by decide +kernel
theorem certified0141 : Certified (graph core0141) (root 8) 2 2 :=
  of_native_maps core0141 DegreeOneMiddleResidualSpectrum299.graph DegreeOneMiddleResidualSpectrum211.graph
    sourceMap0141 fusedMap0141 sourceMap0141_checked fusedMap0141_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0141
#print axioms sourceMap0141_checked
#print axioms fusedMap0141_checked
#print axioms certified0141
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
