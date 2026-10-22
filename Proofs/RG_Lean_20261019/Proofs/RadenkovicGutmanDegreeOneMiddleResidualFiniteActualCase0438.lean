/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0438 : Family 9 := level9.get ⟨438,by decide⟩
def sourceMap0438 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0438 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0438_checked : acceptsGraphIso
    (source (graph core0438) (root 9) 2 2) DegreeOneMiddleResidualSpectrum835.graph sourceMap0438=true := by decide +kernel
theorem fusedMap0438_checked : acceptsGraphIso
    (fused (graph core0438) (root 9) 2 2) DegreeOneMiddleResidualSpectrum655.graph fusedMap0438=true := by decide +kernel
theorem certified0438 : Certified (graph core0438) (root 9) 2 2 :=
  of_native_maps core0438 DegreeOneMiddleResidualSpectrum835.graph DegreeOneMiddleResidualSpectrum655.graph
    sourceMap0438 fusedMap0438 sourceMap0438_checked fusedMap0438_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0438
#print axioms sourceMap0438_checked
#print axioms fusedMap0438_checked
#print axioms certified0438
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
