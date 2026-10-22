/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0479 : Family 9 := level9.get ⟨629,by decide⟩
def sourceMap0479 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0479 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0479_checked : acceptsGraphIso
    (source (graph core0479) (root 9) 2 2) DegreeOneMiddleResidualSpectrum923.graph sourceMap0479=true := by decide +kernel
theorem fusedMap0479_checked : acceptsGraphIso
    (fused (graph core0479) (root 9) 2 2) DegreeOneMiddleResidualSpectrum636.graph fusedMap0479=true := by decide +kernel
theorem certified0479 : Certified (graph core0479) (root 9) 2 2 :=
  of_native_maps core0479 DegreeOneMiddleResidualSpectrum923.graph DegreeOneMiddleResidualSpectrum636.graph
    sourceMap0479 fusedMap0479 sourceMap0479_checked fusedMap0479_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0479
#print axioms sourceMap0479_checked
#print axioms fusedMap0479_checked
#print axioms certified0479
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
