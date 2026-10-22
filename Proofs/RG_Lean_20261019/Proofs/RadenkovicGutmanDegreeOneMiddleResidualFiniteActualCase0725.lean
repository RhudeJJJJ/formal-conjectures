/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0725 : Family 10 := level10.get ⟨344,by decide⟩
def sourceMap0725 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0725 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0725_checked : acceptsGraphIso
    (source (graph core0725) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1813.graph sourceMap0725=true := by decide +kernel
theorem fusedMap0725_checked : acceptsGraphIso
    (fused (graph core0725) (root 10) 2 2) DegreeTwoThreeSpectrum5607.graph fusedMap0725=true := by decide +kernel
theorem certified0725 : Certified (graph core0725) (root 10) 2 2 :=
  of_native_maps core0725 DegreeOneMiddleResidualSpectrum1813.graph DegreeTwoThreeSpectrum5607.graph
    sourceMap0725 fusedMap0725 sourceMap0725_checked fusedMap0725_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0725
#print axioms sourceMap0725_checked
#print axioms fusedMap0725_checked
#print axioms certified0725
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
