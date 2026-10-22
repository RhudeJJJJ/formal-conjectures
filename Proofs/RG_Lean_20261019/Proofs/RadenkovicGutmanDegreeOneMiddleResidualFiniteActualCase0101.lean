/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0101 : Family 8 := level8.get ⟨57,by decide⟩
def sourceMap0101 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0101 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0101_checked : acceptsGraphIso
    (source (graph core0101) (root 8) 2 2) DegreeOneMiddleResidualSpectrum310.graph sourceMap0101=true := by decide +kernel
theorem fusedMap0101_checked : acceptsGraphIso
    (fused (graph core0101) (root 8) 2 2) DegreeOneMiddleResidualSpectrum134.graph fusedMap0101=true := by decide +kernel
theorem certified0101 : Certified (graph core0101) (root 8) 2 2 :=
  of_native_maps core0101 DegreeOneMiddleResidualSpectrum310.graph DegreeOneMiddleResidualSpectrum134.graph
    sourceMap0101 fusedMap0101 sourceMap0101_checked fusedMap0101_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0101
#print axioms sourceMap0101_checked
#print axioms fusedMap0101_checked
#print axioms certified0101
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
