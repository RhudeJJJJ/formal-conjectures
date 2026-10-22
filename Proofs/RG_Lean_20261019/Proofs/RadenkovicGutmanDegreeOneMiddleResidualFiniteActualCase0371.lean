/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0371 : Family 9 := level9.get ⟨270,by decide⟩
def sourceMap0371 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0371 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0371_checked : acceptsGraphIso
    (source (graph core0371) (root 9) 2 2) DegreeOneMiddleResidualSpectrum891.graph sourceMap0371=true := by decide +kernel
theorem fusedMap0371_checked : acceptsGraphIso
    (fused (graph core0371) (root 9) 2 2) DegreeTwoThreeSpectrum4083.graph fusedMap0371=true := by decide +kernel
theorem certified0371 : Certified (graph core0371) (root 9) 2 2 :=
  of_native_maps core0371 DegreeOneMiddleResidualSpectrum891.graph DegreeTwoThreeSpectrum4083.graph
    sourceMap0371 fusedMap0371 sourceMap0371_checked fusedMap0371_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0371
#print axioms sourceMap0371_checked
#print axioms fusedMap0371_checked
#print axioms certified0371
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
