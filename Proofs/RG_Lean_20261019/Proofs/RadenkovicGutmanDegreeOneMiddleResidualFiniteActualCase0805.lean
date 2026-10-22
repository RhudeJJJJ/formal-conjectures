/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0805 : Family 10 := level10.get ⟨502,by decide⟩
def sourceMap0805 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0805 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0805_checked : acceptsGraphIso
    (source (graph core0805) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1972.graph sourceMap0805=true := by decide +kernel
theorem fusedMap0805_checked : acceptsGraphIso
    (fused (graph core0805) (root 10) 2 2) DegreeTwoThreeSpectrum5139.graph fusedMap0805=true := by decide +kernel
theorem certified0805 : Certified (graph core0805) (root 10) 2 2 :=
  of_native_maps core0805 DegreeOneMiddleResidualSpectrum1972.graph DegreeTwoThreeSpectrum5139.graph
    sourceMap0805 fusedMap0805 sourceMap0805_checked fusedMap0805_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0805
#print axioms sourceMap0805_checked
#print axioms fusedMap0805_checked
#print axioms certified0805
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
