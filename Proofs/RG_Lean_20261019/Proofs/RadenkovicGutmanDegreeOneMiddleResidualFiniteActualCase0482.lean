/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0482 : Family 9 := level9.get ⟨649,by decide⟩
def sourceMap0482 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0482 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0482_checked : acceptsGraphIso
    (source (graph core0482) (root 9) 2 2) DegreeOneMiddleResidualSpectrum926.graph sourceMap0482=true := by decide +kernel
theorem fusedMap0482_checked : acceptsGraphIso
    (fused (graph core0482) (root 9) 2 2) DegreeOneMiddleResidualSpectrum654.graph fusedMap0482=true := by decide +kernel
theorem certified0482 : Certified (graph core0482) (root 9) 2 2 :=
  of_native_maps core0482 DegreeOneMiddleResidualSpectrum926.graph DegreeOneMiddleResidualSpectrum654.graph
    sourceMap0482 fusedMap0482 sourceMap0482_checked fusedMap0482_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0482
#print axioms sourceMap0482_checked
#print axioms fusedMap0482_checked
#print axioms certified0482
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
