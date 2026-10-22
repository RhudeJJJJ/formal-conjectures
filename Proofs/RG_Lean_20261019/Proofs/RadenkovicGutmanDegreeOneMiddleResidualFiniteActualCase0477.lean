/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0477 : Family 9 := level9.get ⟨592,by decide⟩
def sourceMap0477 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0477 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0477_checked : acceptsGraphIso
    (source (graph core0477) (root 9) 2 2) DegreeOneMiddleResidualSpectrum921.graph sourceMap0477=true := by decide +kernel
theorem fusedMap0477_checked : acceptsGraphIso
    (fused (graph core0477) (root 9) 2 2) DegreeOneMiddleResidualSpectrum595.graph fusedMap0477=true := by decide +kernel
theorem certified0477 : Certified (graph core0477) (root 9) 2 2 :=
  of_native_maps core0477 DegreeOneMiddleResidualSpectrum921.graph DegreeOneMiddleResidualSpectrum595.graph
    sourceMap0477 fusedMap0477 sourceMap0477_checked fusedMap0477_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0477
#print axioms sourceMap0477_checked
#print axioms fusedMap0477_checked
#print axioms certified0477
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
