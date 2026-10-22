/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0649 : Family 10 := level10.get ⟨226,by decide⟩
def sourceMap0649 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0649 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0649_checked : acceptsGraphIso
    (source (graph core0649) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1641.graph sourceMap0649=true := by decide +kernel
theorem fusedMap0649_checked : acceptsGraphIso
    (fused (graph core0649) (root 10) 2 2) DegreeTwoThreeSpectrum5269.graph fusedMap0649=true := by decide +kernel
theorem certified0649 : Certified (graph core0649) (root 10) 2 2 :=
  of_native_maps core0649 DegreeOneMiddleResidualSpectrum1641.graph DegreeTwoThreeSpectrum5269.graph
    sourceMap0649 fusedMap0649 sourceMap0649_checked fusedMap0649_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0649
#print axioms sourceMap0649_checked
#print axioms fusedMap0649_checked
#print axioms certified0649
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
