/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0828 : Family 10 := level10.get ⟨536,by decide⟩
def sourceMap0828 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0828 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0828_checked : acceptsGraphIso
    (source (graph core0828) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2026.graph sourceMap0828=true := by decide +kernel
theorem fusedMap0828_checked : acceptsGraphIso
    (fused (graph core0828) (root 10) 2 2) DegreeTwoThreeSpectrum5185.graph fusedMap0828=true := by decide +kernel
theorem certified0828 : Certified (graph core0828) (root 10) 2 2 :=
  of_native_maps core0828 DegreeOneMiddleResidualSpectrum2026.graph DegreeTwoThreeSpectrum5185.graph
    sourceMap0828 fusedMap0828 sourceMap0828_checked fusedMap0828_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0828
#print axioms sourceMap0828_checked
#print axioms fusedMap0828_checked
#print axioms certified0828
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
