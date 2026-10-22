/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0146 : Family 8 := level8.get ⟨142,by decide⟩
def sourceMap0146 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0146 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0146_checked : acceptsGraphIso
    (source (graph core0146) (root 8) 2 2) DegreeOneMiddleResidualSpectrum309.graph sourceMap0146=true := by decide +kernel
theorem fusedMap0146_checked : acceptsGraphIso
    (fused (graph core0146) (root 8) 2 2) DegreeTwoThreeSpectrum2695.graph fusedMap0146=true := by decide +kernel
theorem certified0146 : Certified (graph core0146) (root 8) 2 2 :=
  of_native_maps core0146 DegreeOneMiddleResidualSpectrum309.graph DegreeTwoThreeSpectrum2695.graph
    sourceMap0146 fusedMap0146 sourceMap0146_checked fusedMap0146_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0146
#print axioms sourceMap0146_checked
#print axioms fusedMap0146_checked
#print axioms certified0146
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
