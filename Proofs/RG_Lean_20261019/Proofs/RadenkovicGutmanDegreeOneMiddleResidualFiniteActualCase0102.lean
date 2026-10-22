/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0102 : Family 8 := level8.get ⟨58,by decide⟩
def sourceMap0102 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0102 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0102_checked : acceptsGraphIso
    (source (graph core0102) (root 8) 2 2) DegreeOneMiddleResidualSpectrum313.graph sourceMap0102=true := by decide +kernel
theorem fusedMap0102_checked : acceptsGraphIso
    (fused (graph core0102) (root 8) 2 2) DegreeTwoThreeSpectrum2355.graph fusedMap0102=true := by decide +kernel
theorem certified0102 : Certified (graph core0102) (root 8) 2 2 :=
  of_native_maps core0102 DegreeOneMiddleResidualSpectrum313.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap0102 fusedMap0102 sourceMap0102_checked fusedMap0102_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0102
#print axioms sourceMap0102_checked
#print axioms fusedMap0102_checked
#print axioms certified0102
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
