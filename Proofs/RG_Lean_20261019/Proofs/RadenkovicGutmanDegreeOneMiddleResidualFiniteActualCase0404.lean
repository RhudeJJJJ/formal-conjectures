/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0404 : Family 9 := level9.get ⟨346,by decide⟩
def sourceMap0404 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0404 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0404_checked : acceptsGraphIso
    (source (graph core0404) (root 9) 2 2) DegreeOneMiddleResidualSpectrum764.graph sourceMap0404=true := by decide +kernel
theorem fusedMap0404_checked : acceptsGraphIso
    (fused (graph core0404) (root 9) 2 2) DegreeOneMiddleResidualSpectrum584.graph fusedMap0404=true := by decide +kernel
theorem certified0404 : Certified (graph core0404) (root 9) 2 2 :=
  of_native_maps core0404 DegreeOneMiddleResidualSpectrum764.graph DegreeOneMiddleResidualSpectrum584.graph
    sourceMap0404 fusedMap0404 sourceMap0404_checked fusedMap0404_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0404
#print axioms sourceMap0404_checked
#print axioms fusedMap0404_checked
#print axioms certified0404
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
