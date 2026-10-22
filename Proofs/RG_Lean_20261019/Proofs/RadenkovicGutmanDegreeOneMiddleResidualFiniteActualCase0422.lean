/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0422 : Family 9 := level9.get ⟨388,by decide⟩
def sourceMap0422 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0422 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0422_checked : acceptsGraphIso
    (source (graph core0422) (root 9) 2 2) DegreeOneMiddleResidualSpectrum798.graph sourceMap0422=true := by decide +kernel
theorem fusedMap0422_checked : acceptsGraphIso
    (fused (graph core0422) (root 9) 2 2) DegreeTwoThreeSpectrum4336.graph fusedMap0422=true := by decide +kernel
theorem certified0422 : Certified (graph core0422) (root 9) 2 2 :=
  of_native_maps core0422 DegreeOneMiddleResidualSpectrum798.graph DegreeTwoThreeSpectrum4336.graph
    sourceMap0422 fusedMap0422 sourceMap0422_checked fusedMap0422_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0422
#print axioms sourceMap0422_checked
#print axioms fusedMap0422_checked
#print axioms certified0422
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
