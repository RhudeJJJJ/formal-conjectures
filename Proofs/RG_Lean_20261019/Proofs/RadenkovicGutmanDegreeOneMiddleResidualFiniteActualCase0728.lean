/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0728 : Family 10 := level10.get ⟨348,by decide⟩
def sourceMap0728 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0728 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0728_checked : acceptsGraphIso
    (source (graph core0728) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1817.graph sourceMap0728=true := by decide +kernel
theorem fusedMap0728_checked : acceptsGraphIso
    (fused (graph core0728) (root 10) 2 2) DegreeTwoThreeSpectrum5616.graph fusedMap0728=true := by decide +kernel
theorem certified0728 : Certified (graph core0728) (root 10) 2 2 :=
  of_native_maps core0728 DegreeOneMiddleResidualSpectrum1817.graph DegreeTwoThreeSpectrum5616.graph
    sourceMap0728 fusedMap0728 sourceMap0728_checked fusedMap0728_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0728
#print axioms sourceMap0728_checked
#print axioms fusedMap0728_checked
#print axioms certified0728
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
