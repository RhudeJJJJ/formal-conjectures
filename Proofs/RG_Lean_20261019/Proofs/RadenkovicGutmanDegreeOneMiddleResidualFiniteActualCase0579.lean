/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0579 : Family 10 := level10.get ⟨121,by decide⟩
def sourceMap0579 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0579 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0579_checked : acceptsGraphIso
    (source (graph core0579) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1903.graph sourceMap0579=true := by decide +kernel
theorem fusedMap0579_checked : acceptsGraphIso
    (fused (graph core0579) (root 10) 2 2) DegreeTwoThreeSpectrum5050.graph fusedMap0579=true := by decide +kernel
theorem certified0579 : Certified (graph core0579) (root 10) 2 2 :=
  of_native_maps core0579 DegreeOneMiddleResidualSpectrum1903.graph DegreeTwoThreeSpectrum5050.graph
    sourceMap0579 fusedMap0579 sourceMap0579_checked fusedMap0579_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0579
#print axioms sourceMap0579_checked
#print axioms fusedMap0579_checked
#print axioms certified0579
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
