/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0528 : Family 10 := level10.get ⟨54,by decide⟩
def sourceMap0528 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0528 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0528_checked : acceptsGraphIso
    (source (graph core0528) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1571.graph sourceMap0528=true := by decide +kernel
theorem fusedMap0528_checked : acceptsGraphIso
    (fused (graph core0528) (root 10) 2 2) DegreeTwoThreeSpectrum4966.graph fusedMap0528=true := by decide +kernel
theorem certified0528 : Certified (graph core0528) (root 10) 2 2 :=
  of_native_maps core0528 DegreeOneMiddleResidualSpectrum1571.graph DegreeTwoThreeSpectrum4966.graph
    sourceMap0528 fusedMap0528 sourceMap0528_checked fusedMap0528_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0528
#print axioms sourceMap0528_checked
#print axioms fusedMap0528_checked
#print axioms certified0528
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
