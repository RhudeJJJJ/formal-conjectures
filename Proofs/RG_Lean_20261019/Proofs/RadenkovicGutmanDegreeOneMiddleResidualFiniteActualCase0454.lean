/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0454 : Family 9 := level9.get ⟨487,by decide⟩
def sourceMap0454 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0454 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0454_checked : acceptsGraphIso
    (source (graph core0454) (root 9) 2 2) DegreeOneMiddleResidualSpectrum871.graph sourceMap0454=true := by decide +kernel
theorem fusedMap0454_checked : acceptsGraphIso
    (fused (graph core0454) (root 9) 2 2) DegreeOneMiddleResidualSpectrum689.graph fusedMap0454=true := by decide +kernel
theorem certified0454 : Certified (graph core0454) (root 9) 2 2 :=
  of_native_maps core0454 DegreeOneMiddleResidualSpectrum871.graph DegreeOneMiddleResidualSpectrum689.graph
    sourceMap0454 fusedMap0454 sourceMap0454_checked fusedMap0454_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0454
#print axioms sourceMap0454_checked
#print axioms fusedMap0454_checked
#print axioms certified0454
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
