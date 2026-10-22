/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0403 : Family 9 := level9.get ⟨344,by decide⟩
def sourceMap0403 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0403 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0403_checked : acceptsGraphIso
    (source (graph core0403) (root 9) 2 2) DegreeOneMiddleResidualSpectrum762.graph sourceMap0403=true := by decide +kernel
theorem fusedMap0403_checked : acceptsGraphIso
    (fused (graph core0403) (root 9) 2 2) DegreeTwoThreeSpectrum4241.graph fusedMap0403=true := by decide +kernel
theorem certified0403 : Certified (graph core0403) (root 9) 2 2 :=
  of_native_maps core0403 DegreeOneMiddleResidualSpectrum762.graph DegreeTwoThreeSpectrum4241.graph
    sourceMap0403 fusedMap0403 sourceMap0403_checked fusedMap0403_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0403
#print axioms sourceMap0403_checked
#print axioms fusedMap0403_checked
#print axioms certified0403
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
