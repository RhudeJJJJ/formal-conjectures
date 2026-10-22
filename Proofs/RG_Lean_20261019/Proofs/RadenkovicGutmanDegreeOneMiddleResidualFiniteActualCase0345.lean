/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0345 : Family 9 := level9.get ⟨221,by decide⟩
def sourceMap0345 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0345 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0345_checked : acceptsGraphIso
    (source (graph core0345) (root 9) 2 2) DegreeOneMiddleResidualSpectrum849.graph sourceMap0345=true := by decide +kernel
theorem fusedMap0345_checked : acceptsGraphIso
    (fused (graph core0345) (root 9) 2 2) DegreeTwoThreeSpectrum4009.graph fusedMap0345=true := by decide +kernel
theorem certified0345 : Certified (graph core0345) (root 9) 2 2 :=
  of_native_maps core0345 DegreeOneMiddleResidualSpectrum849.graph DegreeTwoThreeSpectrum4009.graph
    sourceMap0345 fusedMap0345 sourceMap0345_checked fusedMap0345_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0345
#print axioms sourceMap0345_checked
#print axioms fusedMap0345_checked
#print axioms certified0345
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
