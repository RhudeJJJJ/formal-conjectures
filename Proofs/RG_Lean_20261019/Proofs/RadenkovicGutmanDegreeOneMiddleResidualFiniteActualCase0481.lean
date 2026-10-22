/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0481 : Family 9 := level9.get ⟨634,by decide⟩
def sourceMap0481 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0481 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0481_checked : acceptsGraphIso
    (source (graph core0481) (root 9) 2 2) DegreeOneMiddleResidualSpectrum925.graph sourceMap0481=true := by decide +kernel
theorem fusedMap0481_checked : acceptsGraphIso
    (fused (graph core0481) (root 9) 2 2) DegreeOneMiddleResidualSpectrum640.graph fusedMap0481=true := by decide +kernel
theorem certified0481 : Certified (graph core0481) (root 9) 2 2 :=
  of_native_maps core0481 DegreeOneMiddleResidualSpectrum925.graph DegreeOneMiddleResidualSpectrum640.graph
    sourceMap0481 fusedMap0481 sourceMap0481_checked fusedMap0481_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0481
#print axioms sourceMap0481_checked
#print axioms fusedMap0481_checked
#print axioms certified0481
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
