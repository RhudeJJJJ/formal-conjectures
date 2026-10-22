/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0206 : Family 9 := level9.get ⟨9,by decide⟩
def sourceMap0206 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0206 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0206_checked : acceptsGraphIso
    (source (graph core0206) (root 9) 2 2) DegreeOneMiddleResidualSpectrum588.graph sourceMap0206=true := by decide +kernel
theorem fusedMap0206_checked : acceptsGraphIso
    (fused (graph core0206) (root 9) 2 2) DegreeTwoThreeSpectrum3854.graph fusedMap0206=true := by decide +kernel
theorem certified0206 : Certified (graph core0206) (root 9) 2 2 :=
  of_native_maps core0206 DegreeOneMiddleResidualSpectrum588.graph DegreeTwoThreeSpectrum3854.graph
    sourceMap0206 fusedMap0206 sourceMap0206_checked fusedMap0206_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0206
#print axioms sourceMap0206_checked
#print axioms fusedMap0206_checked
#print axioms certified0206
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
