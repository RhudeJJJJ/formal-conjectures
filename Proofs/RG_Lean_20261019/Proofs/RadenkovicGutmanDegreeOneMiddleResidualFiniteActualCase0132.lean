/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0132 : Family 8 := level8.get ⟨112,by decide⟩
def sourceMap0132 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0132 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0132_checked : acceptsGraphIso
    (source (graph core0132) (root 8) 2 2) DegreeOneMiddleResidualSpectrum281.graph sourceMap0132=true := by decide +kernel
theorem fusedMap0132_checked : acceptsGraphIso
    (fused (graph core0132) (root 8) 2 2) DegreeOneMiddleResidualSpectrum192.graph fusedMap0132=true := by decide +kernel
theorem certified0132 : Certified (graph core0132) (root 8) 2 2 :=
  of_native_maps core0132 DegreeOneMiddleResidualSpectrum281.graph DegreeOneMiddleResidualSpectrum192.graph
    sourceMap0132 fusedMap0132 sourceMap0132_checked fusedMap0132_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0132
#print axioms sourceMap0132_checked
#print axioms fusedMap0132_checked
#print axioms certified0132
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
