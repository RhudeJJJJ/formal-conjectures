/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0424 : Family 9 := level9.get ⟨391,by decide⟩
def sourceMap0424 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0424 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0424_checked : acceptsGraphIso
    (source (graph core0424) (root 9) 2 2) DegreeOneMiddleResidualSpectrum801.graph sourceMap0424=true := by decide +kernel
theorem fusedMap0424_checked : acceptsGraphIso
    (fused (graph core0424) (root 9) 2 2) DegreeTwoThreeSpectrum4343.graph fusedMap0424=true := by decide +kernel
theorem certified0424 : Certified (graph core0424) (root 9) 2 2 :=
  of_native_maps core0424 DegreeOneMiddleResidualSpectrum801.graph DegreeTwoThreeSpectrum4343.graph
    sourceMap0424 fusedMap0424 sourceMap0424_checked fusedMap0424_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0424
#print axioms sourceMap0424_checked
#print axioms fusedMap0424_checked
#print axioms certified0424
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
