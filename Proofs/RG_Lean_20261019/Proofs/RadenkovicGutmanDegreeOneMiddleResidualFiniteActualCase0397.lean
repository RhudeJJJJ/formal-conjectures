/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0397 : Family 9 := level9.get ⟨334,by decide⟩
def sourceMap0397 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0397 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0397_checked : acceptsGraphIso
    (source (graph core0397) (root 9) 2 2) DegreeOneMiddleResidualSpectrum753.graph sourceMap0397=true := by decide +kernel
theorem fusedMap0397_checked : acceptsGraphIso
    (fused (graph core0397) (root 9) 2 2) DegreeOneMiddleResidualSpectrum576.graph fusedMap0397=true := by decide +kernel
theorem certified0397 : Certified (graph core0397) (root 9) 2 2 :=
  of_native_maps core0397 DegreeOneMiddleResidualSpectrum753.graph DegreeOneMiddleResidualSpectrum576.graph
    sourceMap0397 fusedMap0397 sourceMap0397_checked fusedMap0397_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0397
#print axioms sourceMap0397_checked
#print axioms fusedMap0397_checked
#print axioms certified0397
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
