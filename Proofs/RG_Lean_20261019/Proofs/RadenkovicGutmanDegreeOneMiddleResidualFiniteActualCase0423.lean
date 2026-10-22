/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0423 : Family 9 := level9.get ⟨390,by decide⟩
def sourceMap0423 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0423 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0423_checked : acceptsGraphIso
    (source (graph core0423) (root 9) 2 2) DegreeOneMiddleResidualSpectrum800.graph sourceMap0423=true := by decide +kernel
theorem fusedMap0423_checked : acceptsGraphIso
    (fused (graph core0423) (root 9) 2 2) DegreeTwoThreeSpectrum4341.graph fusedMap0423=true := by decide +kernel
theorem certified0423 : Certified (graph core0423) (root 9) 2 2 :=
  of_native_maps core0423 DegreeOneMiddleResidualSpectrum800.graph DegreeTwoThreeSpectrum4341.graph
    sourceMap0423 fusedMap0423 sourceMap0423_checked fusedMap0423_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0423
#print axioms sourceMap0423_checked
#print axioms fusedMap0423_checked
#print axioms certified0423
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
