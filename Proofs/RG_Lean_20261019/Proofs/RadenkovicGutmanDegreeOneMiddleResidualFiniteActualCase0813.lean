/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0813 : Family 10 := level10.get ⟨512,by decide⟩
def sourceMap0813 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0813 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0813_checked : acceptsGraphIso
    (source (graph core0813) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1988.graph sourceMap0813=true := by decide +kernel
theorem fusedMap0813_checked : acceptsGraphIso
    (fused (graph core0813) (root 10) 2 2) DegreeTwoThreeSpectrum5151.graph fusedMap0813=true := by decide +kernel
theorem certified0813 : Certified (graph core0813) (root 10) 2 2 :=
  of_native_maps core0813 DegreeOneMiddleResidualSpectrum1988.graph DegreeTwoThreeSpectrum5151.graph
    sourceMap0813 fusedMap0813 sourceMap0813_checked fusedMap0813_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0813
#print axioms sourceMap0813_checked
#print axioms fusedMap0813_checked
#print axioms certified0813
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
