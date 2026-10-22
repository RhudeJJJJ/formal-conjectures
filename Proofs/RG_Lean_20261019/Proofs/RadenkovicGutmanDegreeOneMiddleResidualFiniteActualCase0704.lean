/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0704 : Family 10 := level10.get ⟨312,by decide⟩
def sourceMap0704 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0704 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0704_checked : acceptsGraphIso
    (source (graph core0704) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1773.graph sourceMap0704=true := by decide +kernel
theorem fusedMap0704_checked : acceptsGraphIso
    (fused (graph core0704) (root 10) 2 2) DegreeTwoThreeSpectrum5514.graph fusedMap0704=true := by decide +kernel
theorem certified0704 : Certified (graph core0704) (root 10) 2 2 :=
  of_native_maps core0704 DegreeOneMiddleResidualSpectrum1773.graph DegreeTwoThreeSpectrum5514.graph
    sourceMap0704 fusedMap0704 sourceMap0704_checked fusedMap0704_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0704
#print axioms sourceMap0704_checked
#print axioms fusedMap0704_checked
#print axioms certified0704
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
