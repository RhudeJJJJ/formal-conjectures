/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0124 : Family 8 := level8.get ⟨99,by decide⟩
def sourceMap0124 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0124 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0124_checked : acceptsGraphIso
    (source (graph core0124) (root 8) 2 2) DegreeOneMiddleResidualSpectrum267.graph sourceMap0124=true := by decide +kernel
theorem fusedMap0124_checked : acceptsGraphIso
    (fused (graph core0124) (root 8) 2 2) DegreeTwoThreeSpectrum2459.graph fusedMap0124=true := by decide +kernel
theorem certified0124 : Certified (graph core0124) (root 8) 2 2 :=
  of_native_maps core0124 DegreeOneMiddleResidualSpectrum267.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap0124 fusedMap0124 sourceMap0124_checked fusedMap0124_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0124
#print axioms sourceMap0124_checked
#print axioms fusedMap0124_checked
#print axioms certified0124
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
