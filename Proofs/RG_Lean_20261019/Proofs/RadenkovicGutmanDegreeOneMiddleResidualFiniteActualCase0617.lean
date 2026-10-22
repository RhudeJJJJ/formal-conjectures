/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0617 : Family 10 := level10.get ⟨177,by decide⟩
def sourceMap0617 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,9,10,11,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0617 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0617_checked : acceptsGraphIso
    (source (graph core0617) (root 10) 2 2) DegreeTwoThreeSpectrum6859.graph sourceMap0617=true := by decide +kernel
theorem fusedMap0617_checked : acceptsGraphIso
    (fused (graph core0617) (root 10) 2 2) DegreeTwoThreeSpectrum5124.graph fusedMap0617=true := by decide +kernel
theorem certified0617 : Certified (graph core0617) (root 10) 2 2 :=
  of_native_maps core0617 DegreeTwoThreeSpectrum6859.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap0617 fusedMap0617 sourceMap0617_checked fusedMap0617_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0617
#print axioms sourceMap0617_checked
#print axioms fusedMap0617_checked
#print axioms certified0617
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
