/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0270 : Family 9 := level9.get ⟨95,by decide⟩
def sourceMap0270 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0270 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0270_checked : acceptsGraphIso
    (source (graph core0270) (root 9) 2 2) DegreeOneMiddleResidualSpectrum710.graph sourceMap0270=true := by decide +kernel
theorem fusedMap0270_checked : acceptsGraphIso
    (fused (graph core0270) (root 9) 2 2) DegreeTwoThreeSpectrum4071.graph fusedMap0270=true := by decide +kernel
theorem certified0270 : Certified (graph core0270) (root 9) 2 2 :=
  of_native_maps core0270 DegreeOneMiddleResidualSpectrum710.graph DegreeTwoThreeSpectrum4071.graph
    sourceMap0270 fusedMap0270 sourceMap0270_checked fusedMap0270_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0270
#print axioms sourceMap0270_checked
#print axioms fusedMap0270_checked
#print axioms certified0270
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
