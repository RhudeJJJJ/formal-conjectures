/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0500 : Family 10 := level10.get ⟨18,by decide⟩
def sourceMap0500 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0500 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0500_checked : acceptsGraphIso
    (source (graph core0500) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1269.graph sourceMap0500=true := by decide +kernel
theorem fusedMap0500_checked : acceptsGraphIso
    (fused (graph core0500) (root 10) 2 2) DegreeTwoThreeSpectrum5014.graph fusedMap0500=true := by decide +kernel
theorem certified0500 : Certified (graph core0500) (root 10) 2 2 :=
  of_native_maps core0500 DegreeOneMiddleResidualSpectrum1269.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap0500 fusedMap0500 sourceMap0500_checked fusedMap0500_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0500
#print axioms sourceMap0500_checked
#print axioms fusedMap0500_checked
#print axioms certified0500
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
