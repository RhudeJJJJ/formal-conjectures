/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0378 : Family 9 := level9.get ⟨288,by decide⟩
def sourceMap0378 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0378 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0378_checked : acceptsGraphIso
    (source (graph core0378) (root 9) 2 2) DegreeOneMiddleResidualSpectrum898.graph sourceMap0378=true := by decide +kernel
theorem fusedMap0378_checked : acceptsGraphIso
    (fused (graph core0378) (root 9) 2 2) DegreeTwoThreeSpectrum4116.graph fusedMap0378=true := by decide +kernel
theorem certified0378 : Certified (graph core0378) (root 9) 2 2 :=
  of_native_maps core0378 DegreeOneMiddleResidualSpectrum898.graph DegreeTwoThreeSpectrum4116.graph
    sourceMap0378 fusedMap0378 sourceMap0378_checked fusedMap0378_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0378
#print axioms sourceMap0378_checked
#print axioms fusedMap0378_checked
#print axioms certified0378
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
