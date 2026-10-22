/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0460 : Family 9 := level9.get ⟨501,by decide⟩
def sourceMap0460 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0460 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0460_checked : acceptsGraphIso
    (source (graph core0460) (root 9) 2 2) DegreeOneMiddleResidualSpectrum883.graph sourceMap0460=true := by decide +kernel
theorem fusedMap0460_checked : acceptsGraphIso
    (fused (graph core0460) (root 9) 2 2) DegreeOneMiddleResidualSpectrum734.graph fusedMap0460=true := by decide +kernel
theorem certified0460 : Certified (graph core0460) (root 9) 2 2 :=
  of_native_maps core0460 DegreeOneMiddleResidualSpectrum883.graph DegreeOneMiddleResidualSpectrum734.graph
    sourceMap0460 fusedMap0460 sourceMap0460_checked fusedMap0460_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0460
#print axioms sourceMap0460_checked
#print axioms fusedMap0460_checked
#print axioms certified0460
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
