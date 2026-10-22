/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0448 : Family 9 := level9.get ⟨461,by decide⟩
def sourceMap0448 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0448 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0448_checked : acceptsGraphIso
    (source (graph core0448) (root 9) 2 2) DegreeOneMiddleResidualSpectrum854.graph sourceMap0448=true := by decide +kernel
theorem fusedMap0448_checked : acceptsGraphIso
    (fused (graph core0448) (root 9) 2 2) DegreeTwoThreeSpectrum4489.graph fusedMap0448=true := by decide +kernel
theorem certified0448 : Certified (graph core0448) (root 9) 2 2 :=
  of_native_maps core0448 DegreeOneMiddleResidualSpectrum854.graph DegreeTwoThreeSpectrum4489.graph
    sourceMap0448 fusedMap0448 sourceMap0448_checked fusedMap0448_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0448
#print axioms sourceMap0448_checked
#print axioms fusedMap0448_checked
#print axioms certified0448
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
