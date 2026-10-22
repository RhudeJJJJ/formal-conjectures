/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0198 : Family 9 := level9.get ⟨0,by decide⟩
def sourceMap0198 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,4,5,6,7,8,9] (sourceLabel 9 2 2 v)
def fusedMap0198 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (fusedLabel 9 2 2 v)
theorem sourceMap0198_checked : acceptsGraphIso
    (source (graph core0198) (root 9) 2 2) DegreeTwoThreeSpectrum4062.graph sourceMap0198=true := by decide +kernel
theorem fusedMap0198_checked : acceptsGraphIso
    (fused (graph core0198) (root 9) 2 2) DegreeOneMiddleResidualSpectrum358.graph fusedMap0198=true := by decide +kernel
theorem certified0198 : Certified (graph core0198) (root 9) 2 2 :=
  of_native_maps core0198 DegreeTwoThreeSpectrum4062.graph DegreeOneMiddleResidualSpectrum358.graph
    sourceMap0198 fusedMap0198 sourceMap0198_checked fusedMap0198_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0198
#print axioms sourceMap0198_checked
#print axioms fusedMap0198_checked
#print axioms certified0198
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
