/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0421 : Family 9 := level9.get ⟨387,by decide⟩
def sourceMap0421 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0421 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0421_checked : acceptsGraphIso
    (source (graph core0421) (root 9) 2 2) DegreeOneMiddleResidualSpectrum797.graph sourceMap0421=true := by decide +kernel
theorem fusedMap0421_checked : acceptsGraphIso
    (fused (graph core0421) (root 9) 2 2) DegreeTwoThreeSpectrum4334.graph fusedMap0421=true := by decide +kernel
theorem certified0421 : Certified (graph core0421) (root 9) 2 2 :=
  of_native_maps core0421 DegreeOneMiddleResidualSpectrum797.graph DegreeTwoThreeSpectrum4334.graph
    sourceMap0421 fusedMap0421 sourceMap0421_checked fusedMap0421_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0421
#print axioms sourceMap0421_checked
#print axioms fusedMap0421_checked
#print axioms certified0421
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
