/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0173 : Family 8 := level8.get ⟨264,by decide⟩
def sourceMap0173 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap0173 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0173_checked : acceptsGraphIso
    (source (graph core0173) (root 8) 2 2) DegreeOneMiddleResidualSpectrum357.graph sourceMap0173=true := by decide +kernel
theorem fusedMap0173_checked : acceptsGraphIso
    (fused (graph core0173) (root 8) 2 2) DegreeOneMiddleResidualSpectrum261.graph fusedMap0173=true := by decide +kernel
theorem certified0173 : Certified (graph core0173) (root 8) 2 2 :=
  of_native_maps core0173 DegreeOneMiddleResidualSpectrum357.graph DegreeOneMiddleResidualSpectrum261.graph
    sourceMap0173 fusedMap0173 sourceMap0173_checked fusedMap0173_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0173
#print axioms sourceMap0173_checked
#print axioms fusedMap0173_checked
#print axioms certified0173
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
