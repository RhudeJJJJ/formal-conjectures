/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0843 : Family 10 := level10.get ⟨565,by decide⟩
def sourceMap0843 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0843 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0843_checked : acceptsGraphIso
    (source (graph core0843) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2053.graph sourceMap0843=true := by decide +kernel
theorem fusedMap0843_checked : acceptsGraphIso
    (fused (graph core0843) (root 10) 2 2) DegreeTwoThreeSpectrum5229.graph fusedMap0843=true := by decide +kernel
theorem certified0843 : Certified (graph core0843) (root 10) 2 2 :=
  of_native_maps core0843 DegreeOneMiddleResidualSpectrum2053.graph DegreeTwoThreeSpectrum5229.graph
    sourceMap0843 fusedMap0843 sourceMap0843_checked fusedMap0843_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0843
#print axioms sourceMap0843_checked
#print axioms fusedMap0843_checked
#print axioms certified0843
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
