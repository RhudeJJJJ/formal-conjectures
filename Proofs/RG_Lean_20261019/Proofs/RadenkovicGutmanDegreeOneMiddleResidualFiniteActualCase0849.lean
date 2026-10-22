/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0849 : Family 10 := level10.get ⟨573,by decide⟩
def sourceMap0849 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0849 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0849_checked : acceptsGraphIso
    (source (graph core0849) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2063.graph sourceMap0849=true := by decide +kernel
theorem fusedMap0849_checked : acceptsGraphIso
    (fused (graph core0849) (root 10) 2 2) DegreeTwoThreeSpectrum5239.graph fusedMap0849=true := by decide +kernel
theorem certified0849 : Certified (graph core0849) (root 10) 2 2 :=
  of_native_maps core0849 DegreeOneMiddleResidualSpectrum2063.graph DegreeTwoThreeSpectrum5239.graph
    sourceMap0849 fusedMap0849 sourceMap0849_checked fusedMap0849_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0849
#print axioms sourceMap0849_checked
#print axioms fusedMap0849_checked
#print axioms certified0849
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
