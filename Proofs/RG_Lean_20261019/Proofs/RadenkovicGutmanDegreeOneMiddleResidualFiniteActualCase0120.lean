/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0120 : Family 8 := level8.get ⟨87,by decide⟩
def sourceMap0120 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0120 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0120_checked : acceptsGraphIso
    (source (graph core0120) (root 8) 2 2) DegreeOneMiddleResidualSpectrum341.graph sourceMap0120=true := by decide +kernel
theorem fusedMap0120_checked : acceptsGraphIso
    (fused (graph core0120) (root 8) 2 2) DegreeOneMiddleResidualSpectrum162.graph fusedMap0120=true := by decide +kernel
theorem certified0120 : Certified (graph core0120) (root 8) 2 2 :=
  of_native_maps core0120 DegreeOneMiddleResidualSpectrum341.graph DegreeOneMiddleResidualSpectrum162.graph
    sourceMap0120 fusedMap0120 sourceMap0120_checked fusedMap0120_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0120
#print axioms sourceMap0120_checked
#print axioms fusedMap0120_checked
#print axioms certified0120
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
