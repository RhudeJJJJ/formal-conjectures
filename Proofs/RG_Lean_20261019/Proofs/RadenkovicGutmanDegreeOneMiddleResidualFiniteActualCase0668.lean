/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0668 : Family 10 := level10.get ⟨252,by decide⟩
def sourceMap0668 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0668 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0668_checked : acceptsGraphIso
    (source (graph core0668) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1680.graph sourceMap0668=true := by decide +kernel
theorem fusedMap0668_checked : acceptsGraphIso
    (fused (graph core0668) (root 10) 2 2) DegreeTwoThreeSpectrum5348.graph fusedMap0668=true := by decide +kernel
theorem certified0668 : Certified (graph core0668) (root 10) 2 2 :=
  of_native_maps core0668 DegreeOneMiddleResidualSpectrum1680.graph DegreeTwoThreeSpectrum5348.graph
    sourceMap0668 fusedMap0668 sourceMap0668_checked fusedMap0668_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0668
#print axioms sourceMap0668_checked
#print axioms fusedMap0668_checked
#print axioms certified0668
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
