/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0113 : Family 8 := level8.get ⟨75,by decide⟩
def sourceMap0113 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0113 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0113_checked : acceptsGraphIso
    (source (graph core0113) (root 8) 2 2) DegreeOneMiddleResidualSpectrum334.graph sourceMap0113=true := by decide +kernel
theorem fusedMap0113_checked : acceptsGraphIso
    (fused (graph core0113) (root 8) 2 2) DegreeOneMiddleResidualSpectrum151.graph fusedMap0113=true := by decide +kernel
theorem certified0113 : Certified (graph core0113) (root 8) 2 2 :=
  of_native_maps core0113 DegreeOneMiddleResidualSpectrum334.graph DegreeOneMiddleResidualSpectrum151.graph
    sourceMap0113 fusedMap0113 sourceMap0113_checked fusedMap0113_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0113
#print axioms sourceMap0113_checked
#print axioms fusedMap0113_checked
#print axioms certified0113
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
