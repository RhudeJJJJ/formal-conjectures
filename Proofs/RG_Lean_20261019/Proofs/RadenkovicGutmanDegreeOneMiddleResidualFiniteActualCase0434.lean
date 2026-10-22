/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0434 : Family 9 := level9.get ⟨426,by decide⟩
def sourceMap0434 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0434 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0434_checked : acceptsGraphIso
    (source (graph core0434) (root 9) 2 2) DegreeOneMiddleResidualSpectrum826.graph sourceMap0434=true := by decide +kernel
theorem fusedMap0434_checked : acceptsGraphIso
    (fused (graph core0434) (root 9) 2 2) DegreeTwoThreeSpectrum4416.graph fusedMap0434=true := by decide +kernel
theorem certified0434 : Certified (graph core0434) (root 9) 2 2 :=
  of_native_maps core0434 DegreeOneMiddleResidualSpectrum826.graph DegreeTwoThreeSpectrum4416.graph
    sourceMap0434 fusedMap0434 sourceMap0434_checked fusedMap0434_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0434
#print axioms sourceMap0434_checked
#print axioms fusedMap0434_checked
#print axioms certified0434
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
