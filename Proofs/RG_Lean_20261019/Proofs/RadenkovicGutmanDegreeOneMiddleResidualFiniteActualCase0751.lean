/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0751 : Family 10 := level10.get ⟨390,by decide⟩
def sourceMap0751 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0751 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0751_checked : acceptsGraphIso
    (source (graph core0751) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1908.graph sourceMap0751=true := by decide +kernel
theorem fusedMap0751_checked : acceptsGraphIso
    (fused (graph core0751) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1426.graph fusedMap0751=true := by decide +kernel
theorem certified0751 : Certified (graph core0751) (root 10) 2 2 :=
  of_native_maps core0751 DegreeOneMiddleResidualSpectrum1908.graph DegreeOneMiddleResidualSpectrum1426.graph
    sourceMap0751 fusedMap0751 sourceMap0751_checked fusedMap0751_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0751
#print axioms sourceMap0751_checked
#print axioms fusedMap0751_checked
#print axioms certified0751
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
