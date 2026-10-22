/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0405 : Family 9 := level9.get ⟨354,by decide⟩
def sourceMap0405 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0405 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0405_checked : acceptsGraphIso
    (source (graph core0405) (root 9) 2 2) DegreeOneMiddleResidualSpectrum769.graph sourceMap0405=true := by decide +kernel
theorem fusedMap0405_checked : acceptsGraphIso
    (fused (graph core0405) (root 9) 2 2) DegreeTwoThreeSpectrum4261.graph fusedMap0405=true := by decide +kernel
theorem certified0405 : Certified (graph core0405) (root 9) 2 2 :=
  of_native_maps core0405 DegreeOneMiddleResidualSpectrum769.graph DegreeTwoThreeSpectrum4261.graph
    sourceMap0405 fusedMap0405 sourceMap0405_checked fusedMap0405_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0405
#print axioms sourceMap0405_checked
#print axioms fusedMap0405_checked
#print axioms certified0405
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
