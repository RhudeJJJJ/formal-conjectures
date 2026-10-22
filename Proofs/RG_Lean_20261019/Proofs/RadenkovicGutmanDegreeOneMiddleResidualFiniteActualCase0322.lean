/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0322 : Family 9 := level9.get ⟨179,by decide⟩
def sourceMap0322 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0322 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0322_checked : acceptsGraphIso
    (source (graph core0322) (root 9) 2 2) DegreeOneMiddleResidualSpectrum808.graph sourceMap0322=true := by decide +kernel
theorem fusedMap0322_checked : acceptsGraphIso
    (fused (graph core0322) (root 9) 2 2) DegreeOneMiddleResidualSpectrum432.graph fusedMap0322=true := by decide +kernel
theorem certified0322 : Certified (graph core0322) (root 9) 2 2 :=
  of_native_maps core0322 DegreeOneMiddleResidualSpectrum808.graph DegreeOneMiddleResidualSpectrum432.graph
    sourceMap0322 fusedMap0322 sourceMap0322_checked fusedMap0322_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0322
#print axioms sourceMap0322_checked
#print axioms fusedMap0322_checked
#print axioms certified0322
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
