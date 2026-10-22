/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0389 : Family 9 := level9.get ⟨321,by decide⟩
def sourceMap0389 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0389 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0389_checked : acceptsGraphIso
    (source (graph core0389) (root 9) 2 2) DegreeOneMiddleResidualSpectrum741.graph sourceMap0389=true := by decide +kernel
theorem fusedMap0389_checked : acceptsGraphIso
    (fused (graph core0389) (root 9) 2 2) DegreeTwoThreeSpectrum4185.graph fusedMap0389=true := by decide +kernel
theorem certified0389 : Certified (graph core0389) (root 9) 2 2 :=
  of_native_maps core0389 DegreeOneMiddleResidualSpectrum741.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap0389 fusedMap0389 sourceMap0389_checked fusedMap0389_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0389
#print axioms sourceMap0389_checked
#print axioms fusedMap0389_checked
#print axioms certified0389
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
