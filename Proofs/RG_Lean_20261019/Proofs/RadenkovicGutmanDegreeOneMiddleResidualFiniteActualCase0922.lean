/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0922 : Family 10 := level10.get ⟨725,by decide⟩
def sourceMap0922 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0922 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0922_checked : acceptsGraphIso
    (source (graph core0922) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2187.graph sourceMap0922=true := by decide +kernel
theorem fusedMap0922_checked : acceptsGraphIso
    (fused (graph core0922) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1270.graph fusedMap0922=true := by decide +kernel
theorem certified0922 : Certified (graph core0922) (root 10) 2 2 :=
  of_native_maps core0922 DegreeOneMiddleResidualSpectrum2187.graph DegreeOneMiddleResidualSpectrum1270.graph
    sourceMap0922 fusedMap0922 sourceMap0922_checked fusedMap0922_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0922
#print axioms sourceMap0922_checked
#print axioms fusedMap0922_checked
#print axioms certified0922
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
