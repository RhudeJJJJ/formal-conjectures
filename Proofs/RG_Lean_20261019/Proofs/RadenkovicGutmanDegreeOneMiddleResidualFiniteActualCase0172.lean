/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0172 : Family 8 := level8.get ⟨240,by decide⟩
def sourceMap0172 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0172 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0172_checked : acceptsGraphIso
    (source (graph core0172) (root 8) 2 2) DegreeOneMiddleResidualSpectrum356.graph sourceMap0172=true := by decide +kernel
theorem fusedMap0172_checked : acceptsGraphIso
    (fused (graph core0172) (root 8) 2 2) DegreeOneMiddleResidualSpectrum217.graph fusedMap0172=true := by decide +kernel
theorem certified0172 : Certified (graph core0172) (root 8) 2 2 :=
  of_native_maps core0172 DegreeOneMiddleResidualSpectrum356.graph DegreeOneMiddleResidualSpectrum217.graph
    sourceMap0172 fusedMap0172 sourceMap0172_checked fusedMap0172_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0172
#print axioms sourceMap0172_checked
#print axioms fusedMap0172_checked
#print axioms certified0172
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
