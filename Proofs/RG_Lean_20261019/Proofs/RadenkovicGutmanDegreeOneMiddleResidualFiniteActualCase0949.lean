/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0949 : Family 10 := level10.get ⟨772,by decide⟩
def sourceMap0949 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0949 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0949_checked : acceptsGraphIso
    (source (graph core0949) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2236.graph sourceMap0949=true := by decide +kernel
theorem fusedMap0949_checked : acceptsGraphIso
    (fused (graph core0949) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1313.graph fusedMap0949=true := by decide +kernel
theorem certified0949 : Certified (graph core0949) (root 10) 2 2 :=
  of_native_maps core0949 DegreeOneMiddleResidualSpectrum2236.graph DegreeOneMiddleResidualSpectrum1313.graph
    sourceMap0949 fusedMap0949 sourceMap0949_checked fusedMap0949_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0949
#print axioms sourceMap0949_checked
#print axioms fusedMap0949_checked
#print axioms certified0949
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
