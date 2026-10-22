/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0839 : Family 10 := level10.get ⟨560,by decide⟩
def sourceMap0839 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0839 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0839_checked : acceptsGraphIso
    (source (graph core0839) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2043.graph sourceMap0839=true := by decide +kernel
theorem fusedMap0839_checked : acceptsGraphIso
    (fused (graph core0839) (root 10) 2 2) DegreeTwoThreeSpectrum5225.graph fusedMap0839=true := by decide +kernel
theorem certified0839 : Certified (graph core0839) (root 10) 2 2 :=
  of_native_maps core0839 DegreeOneMiddleResidualSpectrum2043.graph DegreeTwoThreeSpectrum5225.graph
    sourceMap0839 fusedMap0839 sourceMap0839_checked fusedMap0839_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0839
#print axioms sourceMap0839_checked
#print axioms fusedMap0839_checked
#print axioms certified0839
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
