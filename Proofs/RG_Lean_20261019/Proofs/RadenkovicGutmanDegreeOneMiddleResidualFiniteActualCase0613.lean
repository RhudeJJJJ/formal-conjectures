/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0613 : Family 10 := level10.get ⟨169,by decide⟩
def sourceMap0613 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0613 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0613_checked : acceptsGraphIso
    (source (graph core0613) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1944.graph sourceMap0613=true := by decide +kernel
theorem fusedMap0613_checked : acceptsGraphIso
    (fused (graph core0613) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1048.graph fusedMap0613=true := by decide +kernel
theorem certified0613 : Certified (graph core0613) (root 10) 2 2 :=
  of_native_maps core0613 DegreeOneMiddleResidualSpectrum1944.graph DegreeOneMiddleResidualSpectrum1048.graph
    sourceMap0613 fusedMap0613 sourceMap0613_checked fusedMap0613_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0613
#print axioms sourceMap0613_checked
#print axioms fusedMap0613_checked
#print axioms certified0613
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
