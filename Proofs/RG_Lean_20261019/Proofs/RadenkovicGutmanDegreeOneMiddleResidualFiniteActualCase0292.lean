/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0292 : Family 9 := level9.get ⟨129,by decide⟩
def sourceMap0292 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0292 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0292_checked : acceptsGraphIso
    (source (graph core0292) (root 9) 2 2) DegreeOneMiddleResidualSpectrum696.graph sourceMap0292=true := by decide +kernel
theorem fusedMap0292_checked : acceptsGraphIso
    (fused (graph core0292) (root 9) 2 2) DegreeOneMiddleResidualSpectrum551.graph fusedMap0292=true := by decide +kernel
theorem certified0292 : Certified (graph core0292) (root 9) 2 2 :=
  of_native_maps core0292 DegreeOneMiddleResidualSpectrum696.graph DegreeOneMiddleResidualSpectrum551.graph
    sourceMap0292 fusedMap0292 sourceMap0292_checked fusedMap0292_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0292
#print axioms sourceMap0292_checked
#print axioms fusedMap0292_checked
#print axioms certified0292
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
