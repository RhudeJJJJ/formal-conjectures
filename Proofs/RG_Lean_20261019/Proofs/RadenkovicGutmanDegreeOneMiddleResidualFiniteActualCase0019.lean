/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0019 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0019 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0019 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0019_checked : acceptsGraphIso
    (source (graph core0019) (root 7) 2 2) DegreeOneMiddleResidualSpectrum058.graph sourceMap0019=true := by decide +kernel
theorem fusedMap0019_checked : acceptsGraphIso
    (fused (graph core0019) (root 7) 2 2) DegreeOneMiddleResidualSpectrum021.graph fusedMap0019=true := by decide +kernel
theorem certified0019 : Certified (graph core0019) (root 7) 2 2 :=
  of_native_maps core0019 DegreeOneMiddleResidualSpectrum058.graph DegreeOneMiddleResidualSpectrum021.graph
    sourceMap0019 fusedMap0019 sourceMap0019_checked fusedMap0019_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0019
#print axioms sourceMap0019_checked
#print axioms fusedMap0019_checked
#print axioms certified0019
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
