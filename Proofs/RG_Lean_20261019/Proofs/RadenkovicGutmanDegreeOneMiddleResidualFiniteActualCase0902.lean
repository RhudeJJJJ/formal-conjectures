/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0902 : Family 10 := level10.get ⟨687,by decide⟩
def sourceMap0902 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0902 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0902_checked : acceptsGraphIso
    (source (graph core0902) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2152.graph sourceMap0902=true := by decide +kernel
theorem fusedMap0902_checked : acceptsGraphIso
    (fused (graph core0902) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1236.graph fusedMap0902=true := by decide +kernel
theorem certified0902 : Certified (graph core0902) (root 10) 2 2 :=
  of_native_maps core0902 DegreeOneMiddleResidualSpectrum2152.graph DegreeOneMiddleResidualSpectrum1236.graph
    sourceMap0902 fusedMap0902 sourceMap0902_checked fusedMap0902_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0902
#print axioms sourceMap0902_checked
#print axioms fusedMap0902_checked
#print axioms certified0902
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
