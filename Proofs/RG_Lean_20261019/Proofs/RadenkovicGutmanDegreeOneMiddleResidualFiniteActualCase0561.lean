/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0561 : Family 10 := level10.get ⟨96,by decide⟩
def sourceMap0561 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0561 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0561_checked : acceptsGraphIso
    (source (graph core0561) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1782.graph sourceMap0561=true := by decide +kernel
theorem fusedMap0561_checked : acceptsGraphIso
    (fused (graph core0561) (root 10) 2 2) DegreeTwoThreeSpectrum5017.graph fusedMap0561=true := by decide +kernel
theorem certified0561 : Certified (graph core0561) (root 10) 2 2 :=
  of_native_maps core0561 DegreeOneMiddleResidualSpectrum1782.graph DegreeTwoThreeSpectrum5017.graph
    sourceMap0561 fusedMap0561 sourceMap0561_checked fusedMap0561_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0561
#print axioms sourceMap0561_checked
#print axioms fusedMap0561_checked
#print axioms certified0561
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
