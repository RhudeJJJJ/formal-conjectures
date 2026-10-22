/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0081 : Family 8 := level8.get ⟨26,by decide⟩
def sourceMap0081 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0081 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0081_checked : acceptsGraphIso
    (source (graph core0081) (root 8) 2 2) DegreeOneMiddleResidualSpectrum245.graph sourceMap0081=true := by decide +kernel
theorem fusedMap0081_checked : acceptsGraphIso
    (fused (graph core0081) (root 8) 2 2) DegreeTwoThreeSpectrum2417.graph fusedMap0081=true := by decide +kernel
theorem certified0081 : Certified (graph core0081) (root 8) 2 2 :=
  of_native_maps core0081 DegreeOneMiddleResidualSpectrum245.graph DegreeTwoThreeSpectrum2417.graph
    sourceMap0081 fusedMap0081 sourceMap0081_checked fusedMap0081_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0081
#print axioms sourceMap0081_checked
#print axioms fusedMap0081_checked
#print axioms certified0081
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
