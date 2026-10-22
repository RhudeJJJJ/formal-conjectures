/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0783 : Family 10 := level10.get ⟨443,by decide⟩
def sourceMap0783 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0783 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0783_checked : acceptsGraphIso
    (source (graph core0783) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1870.graph sourceMap0783=true := by decide +kernel
theorem fusedMap0783_checked : acceptsGraphIso
    (fused (graph core0783) (root 10) 2 2) DegreeTwoThreeSpectrum5861.graph fusedMap0783=true := by decide +kernel
theorem certified0783 : Certified (graph core0783) (root 10) 2 2 :=
  of_native_maps core0783 DegreeOneMiddleResidualSpectrum1870.graph DegreeTwoThreeSpectrum5861.graph
    sourceMap0783 fusedMap0783 sourceMap0783_checked fusedMap0783_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0783
#print axioms sourceMap0783_checked
#print axioms fusedMap0783_checked
#print axioms certified0783
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
