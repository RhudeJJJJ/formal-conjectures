/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0513 : Family 10 := level10.get ⟨33,by decide⟩
def sourceMap0513 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0513 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0513_checked : acceptsGraphIso
    (source (graph core0513) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1385.graph sourceMap0513=true := by decide +kernel
theorem fusedMap0513_checked : acceptsGraphIso
    (fused (graph core0513) (root 10) 2 2) DegreeTwoThreeSpectrum5087.graph fusedMap0513=true := by decide +kernel
theorem certified0513 : Certified (graph core0513) (root 10) 2 2 :=
  of_native_maps core0513 DegreeOneMiddleResidualSpectrum1385.graph DegreeTwoThreeSpectrum5087.graph
    sourceMap0513 fusedMap0513 sourceMap0513_checked fusedMap0513_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0513
#print axioms sourceMap0513_checked
#print axioms fusedMap0513_checked
#print axioms certified0513
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
