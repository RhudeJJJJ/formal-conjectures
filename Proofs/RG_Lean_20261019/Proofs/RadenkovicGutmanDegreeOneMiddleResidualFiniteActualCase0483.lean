/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0483 : Family 9 := level9.get ⟨689,by decide⟩
def sourceMap0483 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0483 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0483_checked : acceptsGraphIso
    (source (graph core0483) (root 9) 2 2) DegreeOneMiddleResidualSpectrum927.graph sourceMap0483=true := by decide +kernel
theorem fusedMap0483_checked : acceptsGraphIso
    (fused (graph core0483) (root 9) 2 2) DegreeOneMiddleResidualSpectrum736.graph fusedMap0483=true := by decide +kernel
theorem certified0483 : Certified (graph core0483) (root 9) 2 2 :=
  of_native_maps core0483 DegreeOneMiddleResidualSpectrum927.graph DegreeOneMiddleResidualSpectrum736.graph
    sourceMap0483 fusedMap0483 sourceMap0483_checked fusedMap0483_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0483
#print axioms sourceMap0483_checked
#print axioms fusedMap0483_checked
#print axioms certified0483
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
