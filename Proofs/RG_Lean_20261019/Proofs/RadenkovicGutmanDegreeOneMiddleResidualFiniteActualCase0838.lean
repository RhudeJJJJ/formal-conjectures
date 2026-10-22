/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0838 : Family 10 := level10.get ⟨559,by decide⟩
def sourceMap0838 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0838 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0838_checked : acceptsGraphIso
    (source (graph core0838) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2040.graph sourceMap0838=true := by decide +kernel
theorem fusedMap0838_checked : acceptsGraphIso
    (fused (graph core0838) (root 10) 2 2) DegreeTwoThreeSpectrum5224.graph fusedMap0838=true := by decide +kernel
theorem certified0838 : Certified (graph core0838) (root 10) 2 2 :=
  of_native_maps core0838 DegreeOneMiddleResidualSpectrum2040.graph DegreeTwoThreeSpectrum5224.graph
    sourceMap0838 fusedMap0838 sourceMap0838_checked fusedMap0838_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0838
#print axioms sourceMap0838_checked
#print axioms fusedMap0838_checked
#print axioms certified0838
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
