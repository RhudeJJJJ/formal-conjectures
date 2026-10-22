/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0475 : Family 9 := level9.get ⟨586,by decide⟩
def sourceMap0475 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0475 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0475_checked : acceptsGraphIso
    (source (graph core0475) (root 9) 2 2) DegreeOneMiddleResidualSpectrum919.graph sourceMap0475=true := by decide +kernel
theorem fusedMap0475_checked : acceptsGraphIso
    (fused (graph core0475) (root 9) 2 2) DegreeOneMiddleResidualSpectrum590.graph fusedMap0475=true := by decide +kernel
theorem certified0475 : Certified (graph core0475) (root 9) 2 2 :=
  of_native_maps core0475 DegreeOneMiddleResidualSpectrum919.graph DegreeOneMiddleResidualSpectrum590.graph
    sourceMap0475 fusedMap0475 sourceMap0475_checked fusedMap0475_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0475
#print axioms sourceMap0475_checked
#print axioms fusedMap0475_checked
#print axioms certified0475
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
