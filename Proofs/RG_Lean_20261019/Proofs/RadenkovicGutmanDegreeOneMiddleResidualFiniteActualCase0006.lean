/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0006 : Family 7 := level7.get ⟨7,by decide⟩
def sourceMap0006 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0006 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0006_checked : acceptsGraphIso
    (source (graph core0006) (root 7) 2 2) DegreeOneMiddleResidualSpectrum062.graph sourceMap0006=true := by decide +kernel
theorem fusedMap0006_checked : acceptsGraphIso
    (fused (graph core0006) (root 7) 2 2) DegreeTwoThreeSpectrum1709.graph fusedMap0006=true := by decide +kernel
theorem certified0006 : Certified (graph core0006) (root 7) 2 2 :=
  of_native_maps core0006 DegreeOneMiddleResidualSpectrum062.graph DegreeTwoThreeSpectrum1709.graph
    sourceMap0006 fusedMap0006 sourceMap0006_checked fusedMap0006_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0006
#print axioms sourceMap0006_checked
#print axioms fusedMap0006_checked
#print axioms certified0006
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
