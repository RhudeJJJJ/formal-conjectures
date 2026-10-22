/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0135 : Family 8 := level8.get ⟨116,by decide⟩
def sourceMap0135 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0135 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0135_checked : acceptsGraphIso
    (source (graph core0135) (root 8) 2 2) DegreeOneMiddleResidualSpectrum286.graph sourceMap0135=true := by decide +kernel
theorem fusedMap0135_checked : acceptsGraphIso
    (fused (graph core0135) (root 8) 2 2) DegreeTwoThreeSpectrum2538.graph fusedMap0135=true := by decide +kernel
theorem certified0135 : Certified (graph core0135) (root 8) 2 2 :=
  of_native_maps core0135 DegreeOneMiddleResidualSpectrum286.graph DegreeTwoThreeSpectrum2538.graph
    sourceMap0135 fusedMap0135 sourceMap0135_checked fusedMap0135_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0135
#print axioms sourceMap0135_checked
#print axioms fusedMap0135_checked
#print axioms certified0135
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
