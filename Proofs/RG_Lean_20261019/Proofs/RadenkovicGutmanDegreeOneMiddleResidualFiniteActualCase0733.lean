/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0733 : Family 10 := level10.get ⟨357,by decide⟩
def sourceMap0733 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0733 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0733_checked : acceptsGraphIso
    (source (graph core0733) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1825.graph sourceMap0733=true := by decide +kernel
theorem fusedMap0733_checked : acceptsGraphIso
    (fused (graph core0733) (root 10) 2 2) DegreeTwoThreeSpectrum5638.graph fusedMap0733=true := by decide +kernel
theorem certified0733 : Certified (graph core0733) (root 10) 2 2 :=
  of_native_maps core0733 DegreeOneMiddleResidualSpectrum1825.graph DegreeTwoThreeSpectrum5638.graph
    sourceMap0733 fusedMap0733 sourceMap0733_checked fusedMap0733_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0733
#print axioms sourceMap0733_checked
#print axioms fusedMap0733_checked
#print axioms certified0733
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
