/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0944 : Family 10 := level10.get ⟨765,by decide⟩
def sourceMap0944 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0944 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0944_checked : acceptsGraphIso
    (source (graph core0944) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2225.graph sourceMap0944=true := by decide +kernel
theorem fusedMap0944_checked : acceptsGraphIso
    (fused (graph core0944) (root 10) 2 2) DegreeTwoThreeSpectrum5542.graph fusedMap0944=true := by decide +kernel
theorem certified0944 : Certified (graph core0944) (root 10) 2 2 :=
  of_native_maps core0944 DegreeOneMiddleResidualSpectrum2225.graph DegreeTwoThreeSpectrum5542.graph
    sourceMap0944 fusedMap0944 sourceMap0944_checked fusedMap0944_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0944
#print axioms sourceMap0944_checked
#print axioms fusedMap0944_checked
#print axioms certified0944
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
