/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0287 : Family 9 := level9.get ⟨120,by decide⟩
def sourceMap0287 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0287 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0287_checked : acceptsGraphIso
    (source (graph core0287) (root 9) 2 2) DegreeOneMiddleResidualSpectrum694.graph sourceMap0287=true := by decide +kernel
theorem fusedMap0287_checked : acceptsGraphIso
    (fused (graph core0287) (root 9) 2 2) DegreeTwoThreeSpectrum4142.graph fusedMap0287=true := by decide +kernel
theorem certified0287 : Certified (graph core0287) (root 9) 2 2 :=
  of_native_maps core0287 DegreeOneMiddleResidualSpectrum694.graph DegreeTwoThreeSpectrum4142.graph
    sourceMap0287 fusedMap0287 sourceMap0287_checked fusedMap0287_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0287
#print axioms sourceMap0287_checked
#print axioms fusedMap0287_checked
#print axioms certified0287
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
