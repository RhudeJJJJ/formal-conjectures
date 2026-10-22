/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0247 : Family 9 := level9.get ⟨61,by decide⟩
def sourceMap0247 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0247 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0247_checked : acceptsGraphIso
    (source (graph core0247) (root 9) 2 2) DegreeOneMiddleResidualSpectrum629.graph sourceMap0247=true := by decide +kernel
theorem fusedMap0247_checked : acceptsGraphIso
    (fused (graph core0247) (root 9) 2 2) DegreeTwoThreeSpectrum3965.graph fusedMap0247=true := by decide +kernel
theorem certified0247 : Certified (graph core0247) (root 9) 2 2 :=
  of_native_maps core0247 DegreeOneMiddleResidualSpectrum629.graph DegreeTwoThreeSpectrum3965.graph
    sourceMap0247 fusedMap0247 sourceMap0247_checked fusedMap0247_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0247
#print axioms sourceMap0247_checked
#print axioms fusedMap0247_checked
#print axioms certified0247
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
