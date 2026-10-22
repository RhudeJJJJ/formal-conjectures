/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0933 : Family 10 := level10.get ⟨741,by decide⟩
def sourceMap0933 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0933 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0933_checked : acceptsGraphIso
    (source (graph core0933) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2210.graph sourceMap0933=true := by decide +kernel
theorem fusedMap0933_checked : acceptsGraphIso
    (fused (graph core0933) (root 10) 2 2) DegreeTwoThreeSpectrum5502.graph fusedMap0933=true := by decide +kernel
theorem certified0933 : Certified (graph core0933) (root 10) 2 2 :=
  of_native_maps core0933 DegreeOneMiddleResidualSpectrum2210.graph DegreeTwoThreeSpectrum5502.graph
    sourceMap0933 fusedMap0933 sourceMap0933_checked fusedMap0933_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0933
#print axioms sourceMap0933_checked
#print axioms fusedMap0933_checked
#print axioms certified0933
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
