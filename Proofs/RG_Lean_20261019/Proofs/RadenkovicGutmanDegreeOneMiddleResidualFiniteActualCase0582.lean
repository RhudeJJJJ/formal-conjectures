/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0582 : Family 10 := level10.get ⟨124,by decide⟩
def sourceMap0582 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0582 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0582_checked : acceptsGraphIso
    (source (graph core0582) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1878.graph sourceMap0582=true := by decide +kernel
theorem fusedMap0582_checked : acceptsGraphIso
    (fused (graph core0582) (root 10) 2 2) DegreeTwoThreeSpectrum5053.graph fusedMap0582=true := by decide +kernel
theorem certified0582 : Certified (graph core0582) (root 10) 2 2 :=
  of_native_maps core0582 DegreeOneMiddleResidualSpectrum1878.graph DegreeTwoThreeSpectrum5053.graph
    sourceMap0582 fusedMap0582 sourceMap0582_checked fusedMap0582_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0582
#print axioms sourceMap0582_checked
#print axioms fusedMap0582_checked
#print axioms certified0582
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
