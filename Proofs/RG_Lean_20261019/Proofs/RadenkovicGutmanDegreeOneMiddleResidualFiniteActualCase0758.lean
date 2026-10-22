/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0758 : Family 10 := level10.get ⟨399,by decide⟩
def sourceMap0758 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0758 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0758_checked : acceptsGraphIso
    (source (graph core0758) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1867.graph sourceMap0758=true := by decide +kernel
theorem fusedMap0758_checked : acceptsGraphIso
    (fused (graph core0758) (root 10) 2 2) DegreeTwoThreeSpectrum5753.graph fusedMap0758=true := by decide +kernel
theorem certified0758 : Certified (graph core0758) (root 10) 2 2 :=
  of_native_maps core0758 DegreeOneMiddleResidualSpectrum1867.graph DegreeTwoThreeSpectrum5753.graph
    sourceMap0758 fusedMap0758 sourceMap0758_checked fusedMap0758_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0758
#print axioms sourceMap0758_checked
#print axioms fusedMap0758_checked
#print axioms certified0758
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
