/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0564 : Family 10 := level10.get ⟨100,by decide⟩
def sourceMap0564 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0564 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0564_checked : acceptsGraphIso
    (source (graph core0564) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1802.graph sourceMap0564=true := by decide +kernel
theorem fusedMap0564_checked : acceptsGraphIso
    (fused (graph core0564) (root 10) 2 2) DegreeTwoThreeSpectrum5022.graph fusedMap0564=true := by decide +kernel
theorem certified0564 : Certified (graph core0564) (root 10) 2 2 :=
  of_native_maps core0564 DegreeOneMiddleResidualSpectrum1802.graph DegreeTwoThreeSpectrum5022.graph
    sourceMap0564 fusedMap0564 sourceMap0564_checked fusedMap0564_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0564
#print axioms sourceMap0564_checked
#print axioms fusedMap0564_checked
#print axioms certified0564
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
