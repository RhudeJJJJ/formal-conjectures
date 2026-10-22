/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0037 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0037 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0037 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0037_checked : acceptsGraphIso
    (source (graph core0037) (root 7) 2 2) DegreeOneMiddleResidualSpectrum094.graph sourceMap0037=true := by decide +kernel
theorem fusedMap0037_checked : acceptsGraphIso
    (fused (graph core0037) (root 7) 2 2) DegreeOneMiddleResidualSpectrum019.graph fusedMap0037=true := by decide +kernel
theorem certified0037 : Certified (graph core0037) (root 7) 2 2 :=
  of_native_maps core0037 DegreeOneMiddleResidualSpectrum094.graph DegreeOneMiddleResidualSpectrum019.graph
    sourceMap0037 fusedMap0037 sourceMap0037_checked fusedMap0037_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0037
#print axioms sourceMap0037_checked
#print axioms fusedMap0037_checked
#print axioms certified0037
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
