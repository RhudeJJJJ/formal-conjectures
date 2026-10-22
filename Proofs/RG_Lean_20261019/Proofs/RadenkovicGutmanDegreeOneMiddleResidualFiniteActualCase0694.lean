/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0694 : Family 10 := level10.get ⟨297,by decide⟩
def sourceMap0694 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0694 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0694_checked : acceptsGraphIso
    (source (graph core0694) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1743.graph sourceMap0694=true := by decide +kernel
theorem fusedMap0694_checked : acceptsGraphIso
    (fused (graph core0694) (root 10) 2 2) DegreeTwoThreeSpectrum5468.graph fusedMap0694=true := by decide +kernel
theorem certified0694 : Certified (graph core0694) (root 10) 2 2 :=
  of_native_maps core0694 DegreeOneMiddleResidualSpectrum1743.graph DegreeTwoThreeSpectrum5468.graph
    sourceMap0694 fusedMap0694 sourceMap0694_checked fusedMap0694_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0694
#print axioms sourceMap0694_checked
#print axioms fusedMap0694_checked
#print axioms certified0694
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
