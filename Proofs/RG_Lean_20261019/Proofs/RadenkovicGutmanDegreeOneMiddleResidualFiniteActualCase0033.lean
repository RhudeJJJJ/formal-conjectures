/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0033 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0033 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap0033 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0033_checked : acceptsGraphIso
    (source (graph core0033) (root 7) 2 2) DegreeOneMiddleResidualSpectrum084.graph sourceMap0033=true := by decide +kernel
theorem fusedMap0033_checked : acceptsGraphIso
    (fused (graph core0033) (root 7) 2 2) DegreeTwoThreeSpectrum1861.graph fusedMap0033=true := by decide +kernel
theorem certified0033 : Certified (graph core0033) (root 7) 2 2 :=
  of_native_maps core0033 DegreeOneMiddleResidualSpectrum084.graph DegreeTwoThreeSpectrum1861.graph
    sourceMap0033 fusedMap0033 sourceMap0033_checked fusedMap0033_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0033
#print axioms sourceMap0033_checked
#print axioms fusedMap0033_checked
#print axioms certified0033
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
