/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0171 : Family 8 := level8.get ⟨232,by decide⟩
def sourceMap0171 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0171 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0171_checked : acceptsGraphIso
    (source (graph core0171) (root 8) 2 2) DegreeOneMiddleResidualSpectrum355.graph sourceMap0171=true := by decide +kernel
theorem fusedMap0171_checked : acceptsGraphIso
    (fused (graph core0171) (root 8) 2 2) DegreeOneMiddleResidualSpectrum210.graph fusedMap0171=true := by decide +kernel
theorem certified0171 : Certified (graph core0171) (root 8) 2 2 :=
  of_native_maps core0171 DegreeOneMiddleResidualSpectrum355.graph DegreeOneMiddleResidualSpectrum210.graph
    sourceMap0171 fusedMap0171 sourceMap0171_checked fusedMap0171_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0171
#print axioms sourceMap0171_checked
#print axioms fusedMap0171_checked
#print axioms certified0171
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
