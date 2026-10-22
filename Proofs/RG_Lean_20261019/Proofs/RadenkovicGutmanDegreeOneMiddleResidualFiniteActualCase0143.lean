/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0143 : Family 8 := level8.get ⟨136,by decide⟩
def sourceMap0143 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0143 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0143_checked : acceptsGraphIso
    (source (graph core0143) (root 8) 2 2) DegreeOneMiddleResidualSpectrum303.graph sourceMap0143=true := by decide +kernel
theorem fusedMap0143_checked : acceptsGraphIso
    (fused (graph core0143) (root 8) 2 2) DegreeTwoThreeSpectrum2665.graph fusedMap0143=true := by decide +kernel
theorem certified0143 : Certified (graph core0143) (root 8) 2 2 :=
  of_native_maps core0143 DegreeOneMiddleResidualSpectrum303.graph DegreeTwoThreeSpectrum2665.graph
    sourceMap0143 fusedMap0143 sourceMap0143_checked fusedMap0143_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0143
#print axioms sourceMap0143_checked
#print axioms fusedMap0143_checked
#print axioms certified0143
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
