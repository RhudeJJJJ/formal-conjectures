/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0569 : Family 10 := level10.get ⟨106,by decide⟩
def sourceMap0569 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0569 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0569_checked : acceptsGraphIso
    (source (graph core0569) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1818.graph sourceMap0569=true := by decide +kernel
theorem fusedMap0569_checked : acceptsGraphIso
    (fused (graph core0569) (root 10) 2 2) DegreeTwoThreeSpectrum5029.graph fusedMap0569=true := by decide +kernel
theorem certified0569 : Certified (graph core0569) (root 10) 2 2 :=
  of_native_maps core0569 DegreeOneMiddleResidualSpectrum1818.graph DegreeTwoThreeSpectrum5029.graph
    sourceMap0569 fusedMap0569 sourceMap0569_checked fusedMap0569_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0569
#print axioms sourceMap0569_checked
#print axioms fusedMap0569_checked
#print axioms certified0569
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
