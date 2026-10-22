/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0272 : Family 9 := level9.get ⟨97,by decide⟩
def sourceMap0272 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0272 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0272_checked : acceptsGraphIso
    (source (graph core0272) (root 9) 2 2) DegreeOneMiddleResidualSpectrum700.graph sourceMap0272=true := by decide +kernel
theorem fusedMap0272_checked : acceptsGraphIso
    (fused (graph core0272) (root 9) 2 2) DegreeTwoThreeSpectrum4078.graph fusedMap0272=true := by decide +kernel
theorem certified0272 : Certified (graph core0272) (root 9) 2 2 :=
  of_native_maps core0272 DegreeOneMiddleResidualSpectrum700.graph DegreeTwoThreeSpectrum4078.graph
    sourceMap0272 fusedMap0272 sourceMap0272_checked fusedMap0272_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0272
#print axioms sourceMap0272_checked
#print axioms fusedMap0272_checked
#print axioms certified0272
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
