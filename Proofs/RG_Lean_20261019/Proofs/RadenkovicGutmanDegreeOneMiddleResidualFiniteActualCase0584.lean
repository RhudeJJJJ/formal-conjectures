/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0584 : Family 10 := level10.get ⟨127,by decide⟩
def sourceMap0584 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0584 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0584_checked : acceptsGraphIso
    (source (graph core0584) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1913.graph sourceMap0584=true := by decide +kernel
theorem fusedMap0584_checked : acceptsGraphIso
    (fused (graph core0584) (root 10) 2 2) DegreeTwoThreeSpectrum5056.graph fusedMap0584=true := by decide +kernel
theorem certified0584 : Certified (graph core0584) (root 10) 2 2 :=
  of_native_maps core0584 DegreeOneMiddleResidualSpectrum1913.graph DegreeTwoThreeSpectrum5056.graph
    sourceMap0584 fusedMap0584 sourceMap0584_checked fusedMap0584_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0584
#print axioms sourceMap0584_checked
#print axioms fusedMap0584_checked
#print axioms certified0584
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
