/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0362 : Family 9 := level9.get ⟨255,by decide⟩
def sourceMap0362 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0362 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0362_checked : acceptsGraphIso
    (source (graph core0362) (root 9) 2 2) DegreeOneMiddleResidualSpectrum879.graph sourceMap0362=true := by decide +kernel
theorem fusedMap0362_checked : acceptsGraphIso
    (fused (graph core0362) (root 9) 2 2) DegreeTwoThreeSpectrum4064.graph fusedMap0362=true := by decide +kernel
theorem certified0362 : Certified (graph core0362) (root 9) 2 2 :=
  of_native_maps core0362 DegreeOneMiddleResidualSpectrum879.graph DegreeTwoThreeSpectrum4064.graph
    sourceMap0362 fusedMap0362 sourceMap0362_checked fusedMap0362_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0362
#print axioms sourceMap0362_checked
#print axioms fusedMap0362_checked
#print axioms certified0362
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
