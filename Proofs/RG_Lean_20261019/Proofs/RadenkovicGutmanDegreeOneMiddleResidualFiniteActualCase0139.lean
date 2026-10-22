/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0139 : Family 8 := level8.get ⟨124,by decide⟩
def sourceMap0139 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0139 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0139_checked : acceptsGraphIso
    (source (graph core0139) (root 8) 2 2) DegreeOneMiddleResidualSpectrum293.graph sourceMap0139=true := by decide +kernel
theorem fusedMap0139_checked : acceptsGraphIso
    (fused (graph core0139) (root 8) 2 2) DegreeOneMiddleResidualSpectrum201.graph fusedMap0139=true := by decide +kernel
theorem certified0139 : Certified (graph core0139) (root 8) 2 2 :=
  of_native_maps core0139 DegreeOneMiddleResidualSpectrum293.graph DegreeOneMiddleResidualSpectrum201.graph
    sourceMap0139 fusedMap0139 sourceMap0139_checked fusedMap0139_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0139
#print axioms sourceMap0139_checked
#print axioms fusedMap0139_checked
#print axioms certified0139
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
