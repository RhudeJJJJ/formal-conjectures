/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0554 : Family 10 := level10.get ⟨88,by decide⟩
def sourceMap0554 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0554 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0554_checked : acceptsGraphIso
    (source (graph core0554) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1740.graph sourceMap0554=true := by decide +kernel
theorem fusedMap0554_checked : acceptsGraphIso
    (fused (graph core0554) (root 10) 2 2) DegreeTwoThreeSpectrum5009.graph fusedMap0554=true := by decide +kernel
theorem certified0554 : Certified (graph core0554) (root 10) 2 2 :=
  of_native_maps core0554 DegreeOneMiddleResidualSpectrum1740.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap0554 fusedMap0554 sourceMap0554_checked fusedMap0554_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0554
#print axioms sourceMap0554_checked
#print axioms fusedMap0554_checked
#print axioms certified0554
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
