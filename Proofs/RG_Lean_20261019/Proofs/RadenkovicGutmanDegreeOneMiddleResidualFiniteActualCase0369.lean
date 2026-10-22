/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0369 : Family 9 := level9.get ⟨267,by decide⟩
def sourceMap0369 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0369 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0369_checked : acceptsGraphIso
    (source (graph core0369) (root 9) 2 2) DegreeOneMiddleResidualSpectrum889.graph sourceMap0369=true := by decide +kernel
theorem fusedMap0369_checked : acceptsGraphIso
    (fused (graph core0369) (root 9) 2 2) DegreeOneMiddleResidualSpectrum515.graph fusedMap0369=true := by decide +kernel
theorem certified0369 : Certified (graph core0369) (root 9) 2 2 :=
  of_native_maps core0369 DegreeOneMiddleResidualSpectrum889.graph DegreeOneMiddleResidualSpectrum515.graph
    sourceMap0369 fusedMap0369 sourceMap0369_checked fusedMap0369_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0369
#print axioms sourceMap0369_checked
#print axioms fusedMap0369_checked
#print axioms certified0369
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
