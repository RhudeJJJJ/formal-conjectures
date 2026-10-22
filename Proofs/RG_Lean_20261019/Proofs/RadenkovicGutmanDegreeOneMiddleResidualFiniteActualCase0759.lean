/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0759 : Family 10 := level10.get ⟨403,by decide⟩
def sourceMap0759 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0759 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0759_checked : acceptsGraphIso
    (source (graph core0759) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1915.graph sourceMap0759=true := by decide +kernel
theorem fusedMap0759_checked : acceptsGraphIso
    (fused (graph core0759) (root 10) 2 2) DegreeTwoThreeSpectrum5765.graph fusedMap0759=true := by decide +kernel
theorem certified0759 : Certified (graph core0759) (root 10) 2 2 :=
  of_native_maps core0759 DegreeOneMiddleResidualSpectrum1915.graph DegreeTwoThreeSpectrum5765.graph
    sourceMap0759 fusedMap0759 sourceMap0759_checked fusedMap0759_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0759
#print axioms sourceMap0759_checked
#print axioms fusedMap0759_checked
#print axioms certified0759
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
