/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0647 : Family 10 := level10.get ⟨223,by decide⟩
def sourceMap0647 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0647 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0647_checked : acceptsGraphIso
    (source (graph core0647) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1631.graph sourceMap0647=true := by decide +kernel
theorem fusedMap0647_checked : acceptsGraphIso
    (fused (graph core0647) (root 10) 2 2) DegreeTwoThreeSpectrum5258.graph fusedMap0647=true := by decide +kernel
theorem certified0647 : Certified (graph core0647) (root 10) 2 2 :=
  of_native_maps core0647 DegreeOneMiddleResidualSpectrum1631.graph DegreeTwoThreeSpectrum5258.graph
    sourceMap0647 fusedMap0647 sourceMap0647_checked fusedMap0647_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0647
#print axioms sourceMap0647_checked
#print axioms fusedMap0647_checked
#print axioms certified0647
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
