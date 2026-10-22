/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0045 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0045 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0045 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0045_checked : acceptsGraphIso
    (source (graph core0045) (root 7) 2 2) DegreeOneMiddleResidualSpectrum102.graph sourceMap0045=true := by decide +kernel
theorem fusedMap0045_checked : acceptsGraphIso
    (fused (graph core0045) (root 7) 2 2) DegreeOneMiddleResidualSpectrum037.graph fusedMap0045=true := by decide +kernel
theorem certified0045 : Certified (graph core0045) (root 7) 2 2 :=
  of_native_maps core0045 DegreeOneMiddleResidualSpectrum102.graph DegreeOneMiddleResidualSpectrum037.graph
    sourceMap0045 fusedMap0045 sourceMap0045_checked fusedMap0045_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0045
#print axioms sourceMap0045_checked
#print axioms fusedMap0045_checked
#print axioms certified0045
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
