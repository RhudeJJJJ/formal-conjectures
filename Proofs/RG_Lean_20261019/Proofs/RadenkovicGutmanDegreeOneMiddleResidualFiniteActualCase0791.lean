/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0791 : Family 10 := level10.get ⟨459,by decide⟩
def sourceMap0791 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0791 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0791_checked : acceptsGraphIso
    (source (graph core0791) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1864.graph sourceMap0791=true := by decide +kernel
theorem fusedMap0791_checked : acceptsGraphIso
    (fused (graph core0791) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1497.graph fusedMap0791=true := by decide +kernel
theorem certified0791 : Certified (graph core0791) (root 10) 2 2 :=
  of_native_maps core0791 DegreeOneMiddleResidualSpectrum1864.graph DegreeOneMiddleResidualSpectrum1497.graph
    sourceMap0791 fusedMap0791 sourceMap0791_checked fusedMap0791_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0791
#print axioms sourceMap0791_checked
#print axioms fusedMap0791_checked
#print axioms certified0791
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
