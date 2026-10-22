/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0426 : Family 9 := level9.get ⟨394,by decide⟩
def sourceMap0426 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0426 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0426_checked : acceptsGraphIso
    (source (graph core0426) (root 9) 2 2) DegreeOneMiddleResidualSpectrum804.graph sourceMap0426=true := by decide +kernel
theorem fusedMap0426_checked : acceptsGraphIso
    (fused (graph core0426) (root 9) 2 2) DegreeOneMiddleResidualSpectrum621.graph fusedMap0426=true := by decide +kernel
theorem certified0426 : Certified (graph core0426) (root 9) 2 2 :=
  of_native_maps core0426 DegreeOneMiddleResidualSpectrum804.graph DegreeOneMiddleResidualSpectrum621.graph
    sourceMap0426 fusedMap0426 sourceMap0426_checked fusedMap0426_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0426
#print axioms sourceMap0426_checked
#print axioms fusedMap0426_checked
#print axioms certified0426
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
