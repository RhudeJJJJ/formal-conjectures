/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0419 : Family 9 := level9.get ⟨378,by decide⟩
def sourceMap0419 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0419 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0419_checked : acceptsGraphIso
    (source (graph core0419) (root 9) 2 2) DegreeOneMiddleResidualSpectrum791.graph sourceMap0419=true := by decide +kernel
theorem fusedMap0419_checked : acceptsGraphIso
    (fused (graph core0419) (root 9) 2 2) DegreeOneMiddleResidualSpectrum610.graph fusedMap0419=true := by decide +kernel
theorem certified0419 : Certified (graph core0419) (root 9) 2 2 :=
  of_native_maps core0419 DegreeOneMiddleResidualSpectrum791.graph DegreeOneMiddleResidualSpectrum610.graph
    sourceMap0419 fusedMap0419 sourceMap0419_checked fusedMap0419_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0419
#print axioms sourceMap0419_checked
#print axioms fusedMap0419_checked
#print axioms certified0419
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
