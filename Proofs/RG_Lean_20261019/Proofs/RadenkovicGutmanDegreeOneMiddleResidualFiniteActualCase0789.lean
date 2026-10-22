/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0789 : Family 10 := level10.get ⟨456,by decide⟩
def sourceMap0789 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0789 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0789_checked : acceptsGraphIso
    (source (graph core0789) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1847.graph sourceMap0789=true := by decide +kernel
theorem fusedMap0789_checked : acceptsGraphIso
    (fused (graph core0789) (root 10) 2 2) DegreeTwoThreeSpectrum5892.graph fusedMap0789=true := by decide +kernel
theorem certified0789 : Certified (graph core0789) (root 10) 2 2 :=
  of_native_maps core0789 DegreeOneMiddleResidualSpectrum1847.graph DegreeTwoThreeSpectrum5892.graph
    sourceMap0789 fusedMap0789 sourceMap0789_checked fusedMap0789_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0789
#print axioms sourceMap0789_checked
#print axioms fusedMap0789_checked
#print axioms certified0789
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
