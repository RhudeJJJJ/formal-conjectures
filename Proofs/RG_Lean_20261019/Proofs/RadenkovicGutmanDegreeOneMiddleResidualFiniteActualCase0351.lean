/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0351 : Family 9 := level9.get ⟨231,by decide⟩
def sourceMap0351 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0351 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0351_checked : acceptsGraphIso
    (source (graph core0351) (root 9) 2 2) DegreeOneMiddleResidualSpectrum862.graph sourceMap0351=true := by decide +kernel
theorem fusedMap0351_checked : acceptsGraphIso
    (fused (graph core0351) (root 9) 2 2) DegreeOneMiddleResidualSpectrum479.graph fusedMap0351=true := by decide +kernel
theorem certified0351 : Certified (graph core0351) (root 9) 2 2 :=
  of_native_maps core0351 DegreeOneMiddleResidualSpectrum862.graph DegreeOneMiddleResidualSpectrum479.graph
    sourceMap0351 fusedMap0351 sourceMap0351_checked fusedMap0351_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0351
#print axioms sourceMap0351_checked
#print axioms fusedMap0351_checked
#print axioms certified0351
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
