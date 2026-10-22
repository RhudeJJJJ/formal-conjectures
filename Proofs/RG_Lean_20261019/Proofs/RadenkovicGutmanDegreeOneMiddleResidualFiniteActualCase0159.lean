/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0159 : Family 8 := level8.get ⟨188,by decide⟩
def sourceMap0159 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0159 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0159_checked : acceptsGraphIso
    (source (graph core0159) (root 8) 2 2) DegreeOneMiddleResidualSpectrum343.graph sourceMap0159=true := by decide +kernel
theorem fusedMap0159_checked : acceptsGraphIso
    (fused (graph core0159) (root 8) 2 2) DegreeOneMiddleResidualSpectrum168.graph fusedMap0159=true := by decide +kernel
theorem certified0159 : Certified (graph core0159) (root 8) 2 2 :=
  of_native_maps core0159 DegreeOneMiddleResidualSpectrum343.graph DegreeOneMiddleResidualSpectrum168.graph
    sourceMap0159 fusedMap0159 sourceMap0159_checked fusedMap0159_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0159
#print axioms sourceMap0159_checked
#print axioms fusedMap0159_checked
#print axioms certified0159
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
