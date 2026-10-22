/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0103 : Family 8 := level8.get ⟨59,by decide⟩
def sourceMap0103 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0103 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0103_checked : acceptsGraphIso
    (source (graph core0103) (root 8) 2 2) DegreeOneMiddleResidualSpectrum314.graph sourceMap0103=true := by decide +kernel
theorem fusedMap0103_checked : acceptsGraphIso
    (fused (graph core0103) (root 8) 2 2) DegreeTwoThreeSpectrum2356.graph fusedMap0103=true := by decide +kernel
theorem certified0103 : Certified (graph core0103) (root 8) 2 2 :=
  of_native_maps core0103 DegreeOneMiddleResidualSpectrum314.graph DegreeTwoThreeSpectrum2356.graph
    sourceMap0103 fusedMap0103 sourceMap0103_checked fusedMap0103_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0103
#print axioms sourceMap0103_checked
#print axioms fusedMap0103_checked
#print axioms certified0103
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
