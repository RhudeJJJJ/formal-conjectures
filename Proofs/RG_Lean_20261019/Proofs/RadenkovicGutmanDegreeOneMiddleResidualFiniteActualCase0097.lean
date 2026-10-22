/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0097 : Family 8 := level8.get ⟨49,by decide⟩
def sourceMap0097 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap0097 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0097_checked : acceptsGraphIso
    (source (graph core0097) (root 8) 2 2) DegreeOneMiddleResidualSpectrum297.graph sourceMap0097=true := by decide +kernel
theorem fusedMap0097_checked : acceptsGraphIso
    (fused (graph core0097) (root 8) 2 2) DegreeTwoThreeSpectrum2335.graph fusedMap0097=true := by decide +kernel
theorem certified0097 : Certified (graph core0097) (root 8) 2 2 :=
  of_native_maps core0097 DegreeOneMiddleResidualSpectrum297.graph DegreeTwoThreeSpectrum2335.graph
    sourceMap0097 fusedMap0097 sourceMap0097_checked fusedMap0097_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0097
#print axioms sourceMap0097_checked
#print axioms fusedMap0097_checked
#print axioms certified0097
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
