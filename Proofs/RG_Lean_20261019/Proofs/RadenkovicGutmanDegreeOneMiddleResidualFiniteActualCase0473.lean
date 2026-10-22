/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0473 : Family 9 := level9.get ⟨569,by decide⟩
def sourceMap0473 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0473 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0473_checked : acceptsGraphIso
    (source (graph core0473) (root 9) 2 2) DegreeOneMiddleResidualSpectrum917.graph sourceMap0473=true := by decide +kernel
theorem fusedMap0473_checked : acceptsGraphIso
    (fused (graph core0473) (root 9) 2 2) DegreeOneMiddleResidualSpectrum575.graph fusedMap0473=true := by decide +kernel
theorem certified0473 : Certified (graph core0473) (root 9) 2 2 :=
  of_native_maps core0473 DegreeOneMiddleResidualSpectrum917.graph DegreeOneMiddleResidualSpectrum575.graph
    sourceMap0473 fusedMap0473 sourceMap0473_checked fusedMap0473_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0473
#print axioms sourceMap0473_checked
#print axioms fusedMap0473_checked
#print axioms certified0473
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
