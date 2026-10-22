/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0309 : Family 9 := level9.get ⟨159,by decide⟩
def sourceMap0309 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0309 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0309_checked : acceptsGraphIso
    (source (graph core0309) (root 9) 2 2) DegreeOneMiddleResidualSpectrum779.graph sourceMap0309=true := by decide +kernel
theorem fusedMap0309_checked : acceptsGraphIso
    (fused (graph core0309) (root 9) 2 2) DegreeTwoThreeSpectrum3920.graph fusedMap0309=true := by decide +kernel
theorem certified0309 : Certified (graph core0309) (root 9) 2 2 :=
  of_native_maps core0309 DegreeOneMiddleResidualSpectrum779.graph DegreeTwoThreeSpectrum3920.graph
    sourceMap0309 fusedMap0309 sourceMap0309_checked fusedMap0309_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0309
#print axioms sourceMap0309_checked
#print axioms fusedMap0309_checked
#print axioms certified0309
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
