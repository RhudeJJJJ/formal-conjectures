/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0615 : Family 10 := level10.get ⟨172,by decide⟩
def sourceMap0615 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0615 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0615_checked : acceptsGraphIso
    (source (graph core0615) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1861.graph sourceMap0615=true := by decide +kernel
theorem fusedMap0615_checked : acceptsGraphIso
    (fused (graph core0615) (root 10) 2 2) DegreeTwoThreeSpectrum5116.graph fusedMap0615=true := by decide +kernel
theorem certified0615 : Certified (graph core0615) (root 10) 2 2 :=
  of_native_maps core0615 DegreeOneMiddleResidualSpectrum1861.graph DegreeTwoThreeSpectrum5116.graph
    sourceMap0615 fusedMap0615 sourceMap0615_checked fusedMap0615_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0615
#print axioms sourceMap0615_checked
#print axioms fusedMap0615_checked
#print axioms certified0615
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
