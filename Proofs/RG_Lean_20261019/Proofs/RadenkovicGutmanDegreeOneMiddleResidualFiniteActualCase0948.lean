/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0948 : Family 10 := level10.get ⟨771,by decide⟩
def sourceMap0948 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0948 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0948_checked : acceptsGraphIso
    (source (graph core0948) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2234.graph sourceMap0948=true := by decide +kernel
theorem fusedMap0948_checked : acceptsGraphIso
    (fused (graph core0948) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1312.graph fusedMap0948=true := by decide +kernel
theorem certified0948 : Certified (graph core0948) (root 10) 2 2 :=
  of_native_maps core0948 DegreeOneMiddleResidualSpectrum2234.graph DegreeOneMiddleResidualSpectrum1312.graph
    sourceMap0948 fusedMap0948 sourceMap0948_checked fusedMap0948_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0948
#print axioms sourceMap0948_checked
#print axioms fusedMap0948_checked
#print axioms certified0948
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
