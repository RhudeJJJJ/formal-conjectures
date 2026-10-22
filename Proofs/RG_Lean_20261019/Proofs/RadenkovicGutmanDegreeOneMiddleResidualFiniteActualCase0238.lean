/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0238 : Family 9 := level9.get ⟨50,by decide⟩
def sourceMap0238 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0238 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0238_checked : acceptsGraphIso
    (source (graph core0238) (root 9) 2 2) DegreeOneMiddleResidualSpectrum606.graph sourceMap0238=true := by decide +kernel
theorem fusedMap0238_checked : acceptsGraphIso
    (fused (graph core0238) (root 9) 2 2) DegreeTwoThreeSpectrum3926.graph fusedMap0238=true := by decide +kernel
theorem certified0238 : Certified (graph core0238) (root 9) 2 2 :=
  of_native_maps core0238 DegreeOneMiddleResidualSpectrum606.graph DegreeTwoThreeSpectrum3926.graph
    sourceMap0238 fusedMap0238 sourceMap0238_checked fusedMap0238_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0238
#print axioms sourceMap0238_checked
#print axioms fusedMap0238_checked
#print axioms certified0238
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
