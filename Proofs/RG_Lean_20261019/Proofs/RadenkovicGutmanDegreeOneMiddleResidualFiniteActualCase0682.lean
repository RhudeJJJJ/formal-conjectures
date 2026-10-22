/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0682 : Family 10 := level10.get ⟨276,by decide⟩
def sourceMap0682 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0682 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0682_checked : acceptsGraphIso
    (source (graph core0682) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1702.graph sourceMap0682=true := by decide +kernel
theorem fusedMap0682_checked : acceptsGraphIso
    (fused (graph core0682) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1227.graph fusedMap0682=true := by decide +kernel
theorem certified0682 : Certified (graph core0682) (root 10) 2 2 :=
  of_native_maps core0682 DegreeOneMiddleResidualSpectrum1702.graph DegreeOneMiddleResidualSpectrum1227.graph
    sourceMap0682 fusedMap0682 sourceMap0682_checked fusedMap0682_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0682
#print axioms sourceMap0682_checked
#print axioms fusedMap0682_checked
#print axioms certified0682
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
