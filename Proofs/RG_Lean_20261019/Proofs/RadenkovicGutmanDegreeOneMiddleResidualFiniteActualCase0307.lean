/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0307 : Family 9 := level9.get ⟨157,by decide⟩
def sourceMap0307 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0307 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0307_checked : acceptsGraphIso
    (source (graph core0307) (root 9) 2 2) DegreeOneMiddleResidualSpectrum775.graph sourceMap0307=true := by decide +kernel
theorem fusedMap0307_checked : acceptsGraphIso
    (fused (graph core0307) (root 9) 2 2) DegreeTwoThreeSpectrum3918.graph fusedMap0307=true := by decide +kernel
theorem certified0307 : Certified (graph core0307) (root 9) 2 2 :=
  of_native_maps core0307 DegreeOneMiddleResidualSpectrum775.graph DegreeTwoThreeSpectrum3918.graph
    sourceMap0307 fusedMap0307 sourceMap0307_checked fusedMap0307_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0307
#print axioms sourceMap0307_checked
#print axioms fusedMap0307_checked
#print axioms certified0307
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
