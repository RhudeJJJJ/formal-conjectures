/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0504 : Family 10 := level10.get ⟨22,by decide⟩
def sourceMap0504 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0504 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0504_checked : acceptsGraphIso
    (source (graph core0504) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1359.graph sourceMap0504=true := by decide +kernel
theorem fusedMap0504_checked : acceptsGraphIso
    (fused (graph core0504) (root 10) 2 2) DegreeTwoThreeSpectrum5038.graph fusedMap0504=true := by decide +kernel
theorem certified0504 : Certified (graph core0504) (root 10) 2 2 :=
  of_native_maps core0504 DegreeOneMiddleResidualSpectrum1359.graph DegreeTwoThreeSpectrum5038.graph
    sourceMap0504 fusedMap0504 sourceMap0504_checked fusedMap0504_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0504
#print axioms sourceMap0504_checked
#print axioms fusedMap0504_checked
#print axioms certified0504
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
