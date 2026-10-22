/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0411 : Family 9 := level9.get ⟨362,by decide⟩
def sourceMap0411 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0411 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0411_checked : acceptsGraphIso
    (source (graph core0411) (root 9) 2 2) DegreeOneMiddleResidualSpectrum777.graph sourceMap0411=true := by decide +kernel
theorem fusedMap0411_checked : acceptsGraphIso
    (fused (graph core0411) (root 9) 2 2) DegreeTwoThreeSpectrum4279.graph fusedMap0411=true := by decide +kernel
theorem certified0411 : Certified (graph core0411) (root 9) 2 2 :=
  of_native_maps core0411 DegreeOneMiddleResidualSpectrum777.graph DegreeTwoThreeSpectrum4279.graph
    sourceMap0411 fusedMap0411 sourceMap0411_checked fusedMap0411_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0411
#print axioms sourceMap0411_checked
#print axioms fusedMap0411_checked
#print axioms certified0411
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
