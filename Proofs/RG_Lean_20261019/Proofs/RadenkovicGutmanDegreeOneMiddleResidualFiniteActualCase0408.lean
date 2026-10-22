/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0408 : Family 9 := level9.get ⟨358,by decide⟩
def sourceMap0408 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0408 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0408_checked : acceptsGraphIso
    (source (graph core0408) (root 9) 2 2) DegreeOneMiddleResidualSpectrum773.graph sourceMap0408=true := by decide +kernel
theorem fusedMap0408_checked : acceptsGraphIso
    (fused (graph core0408) (root 9) 2 2) DegreeOneMiddleResidualSpectrum596.graph fusedMap0408=true := by decide +kernel
theorem certified0408 : Certified (graph core0408) (root 9) 2 2 :=
  of_native_maps core0408 DegreeOneMiddleResidualSpectrum773.graph DegreeOneMiddleResidualSpectrum596.graph
    sourceMap0408 fusedMap0408 sourceMap0408_checked fusedMap0408_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0408
#print axioms sourceMap0408_checked
#print axioms fusedMap0408_checked
#print axioms certified0408
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
