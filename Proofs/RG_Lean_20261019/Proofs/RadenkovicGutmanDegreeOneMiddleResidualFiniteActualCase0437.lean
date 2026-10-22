/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0437 : Family 9 := level9.get ⟨430,by decide⟩
def sourceMap0437 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0437 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0437_checked : acceptsGraphIso
    (source (graph core0437) (root 9) 2 2) DegreeOneMiddleResidualSpectrum830.graph sourceMap0437=true := by decide +kernel
theorem fusedMap0437_checked : acceptsGraphIso
    (fused (graph core0437) (root 9) 2 2) DegreeOneMiddleResidualSpectrum649.graph fusedMap0437=true := by decide +kernel
theorem certified0437 : Certified (graph core0437) (root 9) 2 2 :=
  of_native_maps core0437 DegreeOneMiddleResidualSpectrum830.graph DegreeOneMiddleResidualSpectrum649.graph
    sourceMap0437 fusedMap0437 sourceMap0437_checked fusedMap0437_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0437
#print axioms sourceMap0437_checked
#print axioms fusedMap0437_checked
#print axioms certified0437
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
