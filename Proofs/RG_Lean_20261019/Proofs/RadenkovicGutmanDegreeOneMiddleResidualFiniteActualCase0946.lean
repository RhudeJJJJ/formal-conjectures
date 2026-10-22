/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0946 : Family 10 := level10.get ⟨768,by decide⟩
def sourceMap0946 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0946 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0946_checked : acceptsGraphIso
    (source (graph core0946) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2231.graph sourceMap0946=true := by decide +kernel
theorem fusedMap0946_checked : acceptsGraphIso
    (fused (graph core0946) (root 10) 2 2) DegreeTwoThreeSpectrum5546.graph fusedMap0946=true := by decide +kernel
theorem certified0946 : Certified (graph core0946) (root 10) 2 2 :=
  of_native_maps core0946 DegreeOneMiddleResidualSpectrum2231.graph DegreeTwoThreeSpectrum5546.graph
    sourceMap0946 fusedMap0946 sourceMap0946_checked fusedMap0946_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0946
#print axioms sourceMap0946_checked
#print axioms fusedMap0946_checked
#print axioms certified0946
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
