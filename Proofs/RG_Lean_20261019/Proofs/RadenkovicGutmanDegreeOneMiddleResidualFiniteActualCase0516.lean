/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0516 : Family 10 := level10.get ⟨36,by decide⟩
def sourceMap0516 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0516 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0516_checked : acceptsGraphIso
    (source (graph core0516) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1377.graph sourceMap0516=true := by decide +kernel
theorem fusedMap0516_checked : acceptsGraphIso
    (fused (graph core0516) (root 10) 2 2) DegreeTwoThreeSpectrum5100.graph fusedMap0516=true := by decide +kernel
theorem certified0516 : Certified (graph core0516) (root 10) 2 2 :=
  of_native_maps core0516 DegreeOneMiddleResidualSpectrum1377.graph DegreeTwoThreeSpectrum5100.graph
    sourceMap0516 fusedMap0516 sourceMap0516_checked fusedMap0516_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0516
#print axioms sourceMap0516_checked
#print axioms fusedMap0516_checked
#print axioms certified0516
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
