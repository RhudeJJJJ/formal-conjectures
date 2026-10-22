/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0430 : Family 9 := level9.get ⟨418,by decide⟩
def sourceMap0430 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0430 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0430_checked : acceptsGraphIso
    (source (graph core0430) (root 9) 2 2) DegreeOneMiddleResidualSpectrum819.graph sourceMap0430=true := by decide +kernel
theorem fusedMap0430_checked : acceptsGraphIso
    (fused (graph core0430) (root 9) 2 2) DegreeOneMiddleResidualSpectrum641.graph fusedMap0430=true := by decide +kernel
theorem certified0430 : Certified (graph core0430) (root 9) 2 2 :=
  of_native_maps core0430 DegreeOneMiddleResidualSpectrum819.graph DegreeOneMiddleResidualSpectrum641.graph
    sourceMap0430 fusedMap0430 sourceMap0430_checked fusedMap0430_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0430
#print axioms sourceMap0430_checked
#print axioms fusedMap0430_checked
#print axioms certified0430
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
