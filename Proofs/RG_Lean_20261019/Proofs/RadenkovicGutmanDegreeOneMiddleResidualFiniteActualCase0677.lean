/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0677 : Family 10 := level10.get ⟨267,by decide⟩
def sourceMap0677 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0677 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0677_checked : acceptsGraphIso
    (source (graph core0677) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1694.graph sourceMap0677=true := by decide +kernel
theorem fusedMap0677_checked : acceptsGraphIso
    (fused (graph core0677) (root 10) 2 2) DegreeTwoThreeSpectrum5388.graph fusedMap0677=true := by decide +kernel
theorem certified0677 : Certified (graph core0677) (root 10) 2 2 :=
  of_native_maps core0677 DegreeOneMiddleResidualSpectrum1694.graph DegreeTwoThreeSpectrum5388.graph
    sourceMap0677 fusedMap0677 sourceMap0677_checked fusedMap0677_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0677
#print axioms sourceMap0677_checked
#print axioms fusedMap0677_checked
#print axioms certified0677
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
