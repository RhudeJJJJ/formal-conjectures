/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0376 : Family 9 := level9.get ⟨279,by decide⟩
def sourceMap0376 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0376 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0376_checked : acceptsGraphIso
    (source (graph core0376) (root 9) 2 2) DegreeOneMiddleResidualSpectrum896.graph sourceMap0376=true := by decide +kernel
theorem fusedMap0376_checked : acceptsGraphIso
    (fused (graph core0376) (root 9) 2 2) DegreeOneMiddleResidualSpectrum526.graph fusedMap0376=true := by decide +kernel
theorem certified0376 : Certified (graph core0376) (root 9) 2 2 :=
  of_native_maps core0376 DegreeOneMiddleResidualSpectrum896.graph DegreeOneMiddleResidualSpectrum526.graph
    sourceMap0376 fusedMap0376 sourceMap0376_checked fusedMap0376_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0376
#print axioms sourceMap0376_checked
#print axioms fusedMap0376_checked
#print axioms certified0376
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
