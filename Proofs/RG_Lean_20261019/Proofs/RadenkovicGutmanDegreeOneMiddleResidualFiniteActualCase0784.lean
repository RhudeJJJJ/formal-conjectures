/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0784 : Family 10 := level10.get ⟨447,by decide⟩
def sourceMap0784 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0784 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0784_checked : acceptsGraphIso
    (source (graph core0784) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1936.graph sourceMap0784=true := by decide +kernel
theorem fusedMap0784_checked : acceptsGraphIso
    (fused (graph core0784) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1490.graph fusedMap0784=true := by decide +kernel
theorem certified0784 : Certified (graph core0784) (root 10) 2 2 :=
  of_native_maps core0784 DegreeOneMiddleResidualSpectrum1936.graph DegreeOneMiddleResidualSpectrum1490.graph
    sourceMap0784 fusedMap0784 sourceMap0784_checked fusedMap0784_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0784
#print axioms sourceMap0784_checked
#print axioms fusedMap0784_checked
#print axioms certified0784
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
