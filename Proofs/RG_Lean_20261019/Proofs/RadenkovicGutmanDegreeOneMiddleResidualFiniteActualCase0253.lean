/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0253 : Family 9 := level9.get ⟨71,by decide⟩
def sourceMap0253 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0253 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0253_checked : acceptsGraphIso
    (source (graph core0253) (root 9) 2 2) DegreeOneMiddleResidualSpectrum651.graph sourceMap0253=true := by decide +kernel
theorem fusedMap0253_checked : acceptsGraphIso
    (fused (graph core0253) (root 9) 2 2) DegreeTwoThreeSpectrum3995.graph fusedMap0253=true := by decide +kernel
theorem certified0253 : Certified (graph core0253) (root 9) 2 2 :=
  of_native_maps core0253 DegreeOneMiddleResidualSpectrum651.graph DegreeTwoThreeSpectrum3995.graph
    sourceMap0253 fusedMap0253 sourceMap0253_checked fusedMap0253_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0253
#print axioms sourceMap0253_checked
#print axioms fusedMap0253_checked
#print axioms certified0253
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
