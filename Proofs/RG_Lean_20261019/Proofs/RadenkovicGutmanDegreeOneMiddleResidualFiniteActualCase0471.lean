/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0471 : Family 9 := level9.get ⟨564,by decide⟩
def sourceMap0471 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0471 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0471_checked : acceptsGraphIso
    (source (graph core0471) (root 9) 2 2) DegreeOneMiddleResidualSpectrum915.graph sourceMap0471=true := by decide +kernel
theorem fusedMap0471_checked : acceptsGraphIso
    (fused (graph core0471) (root 9) 2 2) DegreeTwoThreeSpectrum4208.graph fusedMap0471=true := by decide +kernel
theorem certified0471 : Certified (graph core0471) (root 9) 2 2 :=
  of_native_maps core0471 DegreeOneMiddleResidualSpectrum915.graph DegreeTwoThreeSpectrum4208.graph
    sourceMap0471 fusedMap0471 sourceMap0471_checked fusedMap0471_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0471
#print axioms sourceMap0471_checked
#print axioms fusedMap0471_checked
#print axioms certified0471
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
