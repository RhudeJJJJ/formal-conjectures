/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0027 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0027 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0027 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0027_checked : acceptsGraphIso
    (source (graph core0027) (root 7) 2 2) DegreeOneMiddleResidualSpectrum072.graph sourceMap0027=true := by decide +kernel
theorem fusedMap0027_checked : acceptsGraphIso
    (fused (graph core0027) (root 7) 2 2) DegreeTwoThreeSpectrum1807.graph fusedMap0027=true := by decide +kernel
theorem certified0027 : Certified (graph core0027) (root 7) 2 2 :=
  of_native_maps core0027 DegreeOneMiddleResidualSpectrum072.graph DegreeTwoThreeSpectrum1807.graph
    sourceMap0027 fusedMap0027 sourceMap0027_checked fusedMap0027_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0027
#print axioms sourceMap0027_checked
#print axioms fusedMap0027_checked
#print axioms certified0027
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
