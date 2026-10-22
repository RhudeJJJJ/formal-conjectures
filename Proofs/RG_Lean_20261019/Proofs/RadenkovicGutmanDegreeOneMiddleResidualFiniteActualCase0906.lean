/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0906 : Family 10 := level10.get ⟨692,by decide⟩
def sourceMap0906 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0906 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0906_checked : acceptsGraphIso
    (source (graph core0906) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2162.graph sourceMap0906=true := by decide +kernel
theorem fusedMap0906_checked : acceptsGraphIso
    (fused (graph core0906) (root 10) 2 2) DegreeTwoThreeSpectrum5428.graph fusedMap0906=true := by decide +kernel
theorem certified0906 : Certified (graph core0906) (root 10) 2 2 :=
  of_native_maps core0906 DegreeOneMiddleResidualSpectrum2162.graph DegreeTwoThreeSpectrum5428.graph
    sourceMap0906 fusedMap0906 sourceMap0906_checked fusedMap0906_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0906
#print axioms sourceMap0906_checked
#print axioms fusedMap0906_checked
#print axioms certified0906
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
