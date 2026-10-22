/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0959 : Family 10 := level10.get ⟨790,by decide⟩
def sourceMap0959 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0959 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0959_checked : acceptsGraphIso
    (source (graph core0959) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2247.graph sourceMap0959=true := by decide +kernel
theorem fusedMap0959_checked : acceptsGraphIso
    (fused (graph core0959) (root 10) 2 2) DegreeTwoThreeSpectrum5575.graph fusedMap0959=true := by decide +kernel
theorem certified0959 : Certified (graph core0959) (root 10) 2 2 :=
  of_native_maps core0959 DegreeOneMiddleResidualSpectrum2247.graph DegreeTwoThreeSpectrum5575.graph
    sourceMap0959 fusedMap0959 sourceMap0959_checked fusedMap0959_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0959
#print axioms sourceMap0959_checked
#print axioms fusedMap0959_checked
#print axioms certified0959
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
