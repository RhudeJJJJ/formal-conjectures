/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0131 : Family 8 := level8.get ⟨110,by decide⟩
def sourceMap0131 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0131 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0131_checked : acceptsGraphIso
    (source (graph core0131) (root 8) 2 2) DegreeOneMiddleResidualSpectrum279.graph sourceMap0131=true := by decide +kernel
theorem fusedMap0131_checked : acceptsGraphIso
    (fused (graph core0131) (root 8) 2 2) DegreeTwoThreeSpectrum2513.graph fusedMap0131=true := by decide +kernel
theorem certified0131 : Certified (graph core0131) (root 8) 2 2 :=
  of_native_maps core0131 DegreeOneMiddleResidualSpectrum279.graph DegreeTwoThreeSpectrum2513.graph
    sourceMap0131 fusedMap0131 sourceMap0131_checked fusedMap0131_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0131
#print axioms sourceMap0131_checked
#print axioms fusedMap0131_checked
#print axioms certified0131
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
