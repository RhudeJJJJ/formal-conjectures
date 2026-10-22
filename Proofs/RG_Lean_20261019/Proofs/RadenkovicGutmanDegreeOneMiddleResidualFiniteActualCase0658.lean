/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0658 : Family 10 := level10.get ⟨240,by decide⟩
def sourceMap0658 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0658 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0658_checked : acceptsGraphIso
    (source (graph core0658) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1661.graph sourceMap0658=true := by decide +kernel
theorem fusedMap0658_checked : acceptsGraphIso
    (fused (graph core0658) (root 10) 2 2) DegreeTwoThreeSpectrum5310.graph fusedMap0658=true := by decide +kernel
theorem certified0658 : Certified (graph core0658) (root 10) 2 2 :=
  of_native_maps core0658 DegreeOneMiddleResidualSpectrum1661.graph DegreeTwoThreeSpectrum5310.graph
    sourceMap0658 fusedMap0658 sourceMap0658_checked fusedMap0658_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0658
#print axioms sourceMap0658_checked
#print axioms fusedMap0658_checked
#print axioms certified0658
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
