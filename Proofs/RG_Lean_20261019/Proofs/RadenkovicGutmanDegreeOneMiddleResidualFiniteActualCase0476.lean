/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0476 : Family 9 := level9.get ⟨590,by decide⟩
def sourceMap0476 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0476 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0476_checked : acceptsGraphIso
    (source (graph core0476) (root 9) 2 2) DegreeOneMiddleResidualSpectrum920.graph sourceMap0476=true := by decide +kernel
theorem fusedMap0476_checked : acceptsGraphIso
    (fused (graph core0476) (root 9) 2 2) DegreeOneMiddleResidualSpectrum593.graph fusedMap0476=true := by decide +kernel
theorem certified0476 : Certified (graph core0476) (root 9) 2 2 :=
  of_native_maps core0476 DegreeOneMiddleResidualSpectrum920.graph DegreeOneMiddleResidualSpectrum593.graph
    sourceMap0476 fusedMap0476 sourceMap0476_checked fusedMap0476_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0476
#print axioms sourceMap0476_checked
#print axioms fusedMap0476_checked
#print axioms certified0476
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
