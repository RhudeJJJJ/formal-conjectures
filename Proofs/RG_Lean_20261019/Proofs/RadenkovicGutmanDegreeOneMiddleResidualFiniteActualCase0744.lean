/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0744 : Family 10 := level10.get ⟨378,by decide⟩
def sourceMap0744 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0744 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0744_checked : acceptsGraphIso
    (source (graph core0744) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1902.graph sourceMap0744=true := by decide +kernel
theorem fusedMap0744_checked : acceptsGraphIso
    (fused (graph core0744) (root 10) 2 2) DegreeTwoThreeSpectrum5697.graph fusedMap0744=true := by decide +kernel
theorem certified0744 : Certified (graph core0744) (root 10) 2 2 :=
  of_native_maps core0744 DegreeOneMiddleResidualSpectrum1902.graph DegreeTwoThreeSpectrum5697.graph
    sourceMap0744 fusedMap0744 sourceMap0744_checked fusedMap0744_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0744
#print axioms sourceMap0744_checked
#print axioms fusedMap0744_checked
#print axioms certified0744
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
