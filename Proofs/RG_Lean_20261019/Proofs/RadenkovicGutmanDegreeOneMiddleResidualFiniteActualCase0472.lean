/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0472 : Family 9 := level9.get ⟨565,by decide⟩
def sourceMap0472 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0472 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0472_checked : acceptsGraphIso
    (source (graph core0472) (root 9) 2 2) DegreeOneMiddleResidualSpectrum916.graph sourceMap0472=true := by decide +kernel
theorem fusedMap0472_checked : acceptsGraphIso
    (fused (graph core0472) (root 9) 2 2) DegreeOneMiddleResidualSpectrum572.graph fusedMap0472=true := by decide +kernel
theorem certified0472 : Certified (graph core0472) (root 9) 2 2 :=
  of_native_maps core0472 DegreeOneMiddleResidualSpectrum916.graph DegreeOneMiddleResidualSpectrum572.graph
    sourceMap0472 fusedMap0472 sourceMap0472_checked fusedMap0472_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0472
#print axioms sourceMap0472_checked
#print axioms fusedMap0472_checked
#print axioms certified0472
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
