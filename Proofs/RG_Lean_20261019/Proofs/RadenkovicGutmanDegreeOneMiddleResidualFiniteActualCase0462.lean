/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0462 : Family 9 := level9.get ⟨542,by decide⟩
def sourceMap0462 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0462 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0462_checked : acceptsGraphIso
    (source (graph core0462) (root 9) 2 2) DegreeOneMiddleResidualSpectrum906.graph sourceMap0462=true := by decide +kernel
theorem fusedMap0462_checked : acceptsGraphIso
    (fused (graph core0462) (root 9) 2 2) DegreeOneMiddleResidualSpectrum552.graph fusedMap0462=true := by decide +kernel
theorem certified0462 : Certified (graph core0462) (root 9) 2 2 :=
  of_native_maps core0462 DegreeOneMiddleResidualSpectrum906.graph DegreeOneMiddleResidualSpectrum552.graph
    sourceMap0462 fusedMap0462 sourceMap0462_checked fusedMap0462_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0462
#print axioms sourceMap0462_checked
#print axioms fusedMap0462_checked
#print axioms certified0462
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
