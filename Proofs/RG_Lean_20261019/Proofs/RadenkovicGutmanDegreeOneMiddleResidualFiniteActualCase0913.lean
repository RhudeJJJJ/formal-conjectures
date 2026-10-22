/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0913 : Family 10 := level10.get ⟨703,by decide⟩
def sourceMap0913 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0913 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0913_checked : acceptsGraphIso
    (source (graph core0913) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2175.graph sourceMap0913=true := by decide +kernel
theorem fusedMap0913_checked : acceptsGraphIso
    (fused (graph core0913) (root 10) 2 2) DegreeTwoThreeSpectrum5444.graph fusedMap0913=true := by decide +kernel
theorem certified0913 : Certified (graph core0913) (root 10) 2 2 :=
  of_native_maps core0913 DegreeOneMiddleResidualSpectrum2175.graph DegreeTwoThreeSpectrum5444.graph
    sourceMap0913 fusedMap0913 sourceMap0913_checked fusedMap0913_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0913
#print axioms sourceMap0913_checked
#print axioms fusedMap0913_checked
#print axioms certified0913
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
