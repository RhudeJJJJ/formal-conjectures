/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0268 : Family 9 := level9.get ⟨93,by decide⟩
def sourceMap0268 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0268 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0268_checked : acceptsGraphIso
    (source (graph core0268) (root 9) 2 2) DegreeOneMiddleResidualSpectrum708.graph sourceMap0268=true := by decide +kernel
theorem fusedMap0268_checked : acceptsGraphIso
    (fused (graph core0268) (root 9) 2 2) DegreeTwoThreeSpectrum4062.graph fusedMap0268=true := by decide +kernel
theorem certified0268 : Certified (graph core0268) (root 9) 2 2 :=
  of_native_maps core0268 DegreeOneMiddleResidualSpectrum708.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap0268 fusedMap0268 sourceMap0268_checked fusedMap0268_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0268
#print axioms sourceMap0268_checked
#print axioms fusedMap0268_checked
#print axioms certified0268
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
