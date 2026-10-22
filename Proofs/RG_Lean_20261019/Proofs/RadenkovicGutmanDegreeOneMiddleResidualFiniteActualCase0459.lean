/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0459 : Family 9 := level9.get ⟨499,by decide⟩
def sourceMap0459 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0459 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0459_checked : acceptsGraphIso
    (source (graph core0459) (root 9) 2 2) DegreeOneMiddleResidualSpectrum881.graph sourceMap0459=true := by decide +kernel
theorem fusedMap0459_checked : acceptsGraphIso
    (fused (graph core0459) (root 9) 2 2) DegreeOneMiddleResidualSpectrum733.graph fusedMap0459=true := by decide +kernel
theorem certified0459 : Certified (graph core0459) (root 9) 2 2 :=
  of_native_maps core0459 DegreeOneMiddleResidualSpectrum881.graph DegreeOneMiddleResidualSpectrum733.graph
    sourceMap0459 fusedMap0459 sourceMap0459_checked fusedMap0459_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0459
#print axioms sourceMap0459_checked
#print axioms fusedMap0459_checked
#print axioms certified0459
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
