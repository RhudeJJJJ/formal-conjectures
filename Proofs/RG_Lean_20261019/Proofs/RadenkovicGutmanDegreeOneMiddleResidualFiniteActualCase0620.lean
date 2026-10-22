/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0620 : Family 10 := level10.get ⟨181,by decide⟩
def sourceMap0620 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,9,10,11,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0620 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0620_checked : acceptsGraphIso
    (source (graph core0620) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1865.graph sourceMap0620=true := by decide +kernel
theorem fusedMap0620_checked : acceptsGraphIso
    (fused (graph core0620) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1059.graph fusedMap0620=true := by decide +kernel
theorem certified0620 : Certified (graph core0620) (root 10) 2 2 :=
  of_native_maps core0620 DegreeOneMiddleResidualSpectrum1865.graph DegreeOneMiddleResidualSpectrum1059.graph
    sourceMap0620 fusedMap0620 sourceMap0620_checked fusedMap0620_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0620
#print axioms sourceMap0620_checked
#print axioms fusedMap0620_checked
#print axioms certified0620
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
