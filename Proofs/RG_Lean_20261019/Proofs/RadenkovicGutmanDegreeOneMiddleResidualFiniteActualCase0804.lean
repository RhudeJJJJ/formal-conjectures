/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0804 : Family 10 := level10.get ⟨500,by decide⟩
def sourceMap0804 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0804 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0804_checked : acceptsGraphIso
    (source (graph core0804) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1968.graph sourceMap0804=true := by decide +kernel
theorem fusedMap0804_checked : acceptsGraphIso
    (fused (graph core0804) (root 10) 2 2) DegreeTwoThreeSpectrum5137.graph fusedMap0804=true := by decide +kernel
theorem certified0804 : Certified (graph core0804) (root 10) 2 2 :=
  of_native_maps core0804 DegreeOneMiddleResidualSpectrum1968.graph DegreeTwoThreeSpectrum5137.graph
    sourceMap0804 fusedMap0804 sourceMap0804_checked fusedMap0804_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0804
#print axioms sourceMap0804_checked
#print axioms fusedMap0804_checked
#print axioms certified0804
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
