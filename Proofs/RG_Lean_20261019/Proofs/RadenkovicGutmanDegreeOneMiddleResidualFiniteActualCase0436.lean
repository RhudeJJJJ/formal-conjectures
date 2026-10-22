/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0436 : Family 9 := level9.get ⟨428,by decide⟩
def sourceMap0436 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0436 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0436_checked : acceptsGraphIso
    (source (graph core0436) (root 9) 2 2) DegreeOneMiddleResidualSpectrum828.graph sourceMap0436=true := by decide +kernel
theorem fusedMap0436_checked : acceptsGraphIso
    (fused (graph core0436) (root 9) 2 2) DegreeTwoThreeSpectrum4421.graph fusedMap0436=true := by decide +kernel
theorem certified0436 : Certified (graph core0436) (root 9) 2 2 :=
  of_native_maps core0436 DegreeOneMiddleResidualSpectrum828.graph DegreeTwoThreeSpectrum4421.graph
    sourceMap0436 fusedMap0436 sourceMap0436_checked fusedMap0436_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0436
#print axioms sourceMap0436_checked
#print axioms fusedMap0436_checked
#print axioms certified0436
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
