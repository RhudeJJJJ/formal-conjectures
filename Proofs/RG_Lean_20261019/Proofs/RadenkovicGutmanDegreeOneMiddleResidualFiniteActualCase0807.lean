/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0807 : Family 10 := level10.get ⟨504,by decide⟩
def sourceMap0807 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0807 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0807_checked : acceptsGraphIso
    (source (graph core0807) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1978.graph sourceMap0807=true := by decide +kernel
theorem fusedMap0807_checked : acceptsGraphIso
    (fused (graph core0807) (root 10) 2 2) DegreeTwoThreeSpectrum5141.graph fusedMap0807=true := by decide +kernel
theorem certified0807 : Certified (graph core0807) (root 10) 2 2 :=
  of_native_maps core0807 DegreeOneMiddleResidualSpectrum1978.graph DegreeTwoThreeSpectrum5141.graph
    sourceMap0807 fusedMap0807 sourceMap0807_checked fusedMap0807_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0807
#print axioms sourceMap0807_checked
#print axioms fusedMap0807_checked
#print axioms certified0807
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
