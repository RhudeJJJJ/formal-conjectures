/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0458 : Family 9 := level9.get ⟨495,by decide⟩
def sourceMap0458 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0458 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0458_checked : acceptsGraphIso
    (source (graph core0458) (root 9) 2 2) DegreeOneMiddleResidualSpectrum878.graph sourceMap0458=true := by decide +kernel
theorem fusedMap0458_checked : acceptsGraphIso
    (fused (graph core0458) (root 9) 2 2) DegreeOneMiddleResidualSpectrum732.graph fusedMap0458=true := by decide +kernel
theorem certified0458 : Certified (graph core0458) (root 9) 2 2 :=
  of_native_maps core0458 DegreeOneMiddleResidualSpectrum878.graph DegreeOneMiddleResidualSpectrum732.graph
    sourceMap0458 fusedMap0458 sourceMap0458_checked fusedMap0458_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0458
#print axioms sourceMap0458_checked
#print axioms fusedMap0458_checked
#print axioms certified0458
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
