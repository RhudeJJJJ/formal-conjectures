/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0508 : Family 10 := level10.get ⟨27,by decide⟩
def sourceMap0508 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0508 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0508_checked : acceptsGraphIso
    (source (graph core0508) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1381.graph sourceMap0508=true := by decide +kernel
theorem fusedMap0508_checked : acceptsGraphIso
    (fused (graph core0508) (root 10) 2 2) DegreeTwoThreeSpectrum5060.graph fusedMap0508=true := by decide +kernel
theorem certified0508 : Certified (graph core0508) (root 10) 2 2 :=
  of_native_maps core0508 DegreeOneMiddleResidualSpectrum1381.graph DegreeTwoThreeSpectrum5060.graph
    sourceMap0508 fusedMap0508 sourceMap0508_checked fusedMap0508_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0508
#print axioms sourceMap0508_checked
#print axioms fusedMap0508_checked
#print axioms certified0508
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
