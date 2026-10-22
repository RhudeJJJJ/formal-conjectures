/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0760 : Family 10 := level10.get ⟨404,by decide⟩
def sourceMap0760 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0760 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0760_checked : acceptsGraphIso
    (source (graph core0760) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1916.graph sourceMap0760=true := by decide +kernel
theorem fusedMap0760_checked : acceptsGraphIso
    (fused (graph core0760) (root 10) 2 2) DegreeTwoThreeSpectrum5769.graph fusedMap0760=true := by decide +kernel
theorem certified0760 : Certified (graph core0760) (root 10) 2 2 :=
  of_native_maps core0760 DegreeOneMiddleResidualSpectrum1916.graph DegreeTwoThreeSpectrum5769.graph
    sourceMap0760 fusedMap0760 sourceMap0760_checked fusedMap0760_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0760
#print axioms sourceMap0760_checked
#print axioms fusedMap0760_checked
#print axioms certified0760
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
