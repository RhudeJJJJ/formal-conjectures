/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0441 : Family 9 := level9.get ⟨442,by decide⟩
def sourceMap0441 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0441 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0441_checked : acceptsGraphIso
    (source (graph core0441) (root 9) 2 2) DegreeOneMiddleResidualSpectrum839.graph sourceMap0441=true := by decide +kernel
theorem fusedMap0441_checked : acceptsGraphIso
    (fused (graph core0441) (root 9) 2 2) DegreeTwoThreeSpectrum4449.graph fusedMap0441=true := by decide +kernel
theorem certified0441 : Certified (graph core0441) (root 9) 2 2 :=
  of_native_maps core0441 DegreeOneMiddleResidualSpectrum839.graph DegreeTwoThreeSpectrum4449.graph
    sourceMap0441 fusedMap0441 sourceMap0441_checked fusedMap0441_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0441
#print axioms sourceMap0441_checked
#print axioms fusedMap0441_checked
#print axioms certified0441
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
