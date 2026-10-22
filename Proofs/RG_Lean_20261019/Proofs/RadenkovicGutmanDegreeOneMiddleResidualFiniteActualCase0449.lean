/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0449 : Family 9 := level9.get ⟨462,by decide⟩
def sourceMap0449 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0449 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0449_checked : acceptsGraphIso
    (source (graph core0449) (root 9) 2 2) DegreeOneMiddleResidualSpectrum855.graph sourceMap0449=true := by decide +kernel
theorem fusedMap0449_checked : acceptsGraphIso
    (fused (graph core0449) (root 9) 2 2) DegreeTwoThreeSpectrum4491.graph fusedMap0449=true := by decide +kernel
theorem certified0449 : Certified (graph core0449) (root 9) 2 2 :=
  of_native_maps core0449 DegreeOneMiddleResidualSpectrum855.graph DegreeTwoThreeSpectrum4491.graph
    sourceMap0449 fusedMap0449 sourceMap0449_checked fusedMap0449_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0449
#print axioms sourceMap0449_checked
#print axioms fusedMap0449_checked
#print axioms certified0449
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
