/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0367 : Family 9 := level9.get ⟨262,by decide⟩
def sourceMap0367 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0367 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0367_checked : acceptsGraphIso
    (source (graph core0367) (root 9) 2 2) DegreeOneMiddleResidualSpectrum886.graph sourceMap0367=true := by decide +kernel
theorem fusedMap0367_checked : acceptsGraphIso
    (fused (graph core0367) (root 9) 2 2) DegreeTwoThreeSpectrum4072.graph fusedMap0367=true := by decide +kernel
theorem certified0367 : Certified (graph core0367) (root 9) 2 2 :=
  of_native_maps core0367 DegreeOneMiddleResidualSpectrum886.graph DegreeTwoThreeSpectrum4072.graph
    sourceMap0367 fusedMap0367 sourceMap0367_checked fusedMap0367_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0367
#print axioms sourceMap0367_checked
#print axioms fusedMap0367_checked
#print axioms certified0367
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
