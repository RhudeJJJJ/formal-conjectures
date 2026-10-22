/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0217 : Family 9 := level9.get ⟨21,by decide⟩
def sourceMap0217 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0217 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0217_checked : acceptsGraphIso
    (source (graph core0217) (root 9) 2 2) DegreeOneMiddleResidualSpectrum686.graph sourceMap0217=true := by decide +kernel
theorem fusedMap0217_checked : acceptsGraphIso
    (fused (graph core0217) (root 9) 2 2) DegreeTwoThreeSpectrum3867.graph fusedMap0217=true := by decide +kernel
theorem certified0217 : Certified (graph core0217) (root 9) 2 2 :=
  of_native_maps core0217 DegreeOneMiddleResidualSpectrum686.graph DegreeTwoThreeSpectrum3867.graph
    sourceMap0217 fusedMap0217 sourceMap0217_checked fusedMap0217_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0217
#print axioms sourceMap0217_checked
#print axioms fusedMap0217_checked
#print axioms certified0217
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
