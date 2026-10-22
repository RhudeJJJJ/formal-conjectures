/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0942 : Family 10 := level10.get ⟨763,by decide⟩
def sourceMap0942 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0942 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0942_checked : acceptsGraphIso
    (source (graph core0942) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2221.graph sourceMap0942=true := by decide +kernel
theorem fusedMap0942_checked : acceptsGraphIso
    (fused (graph core0942) (root 10) 2 2) DegreeTwoThreeSpectrum5540.graph fusedMap0942=true := by decide +kernel
theorem certified0942 : Certified (graph core0942) (root 10) 2 2 :=
  of_native_maps core0942 DegreeOneMiddleResidualSpectrum2221.graph DegreeTwoThreeSpectrum5540.graph
    sourceMap0942 fusedMap0942 sourceMap0942_checked fusedMap0942_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0942
#print axioms sourceMap0942_checked
#print axioms fusedMap0942_checked
#print axioms certified0942
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
