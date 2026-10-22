/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0029 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0029 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0029 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0029_checked : acceptsGraphIso
    (source (graph core0029) (root 7) 2 2) DegreeOneMiddleResidualSpectrum076.graph sourceMap0029=true := by decide +kernel
theorem fusedMap0029_checked : acceptsGraphIso
    (fused (graph core0029) (root 7) 2 2) DegreeOneMiddleResidualSpectrum041.graph fusedMap0029=true := by decide +kernel
theorem certified0029 : Certified (graph core0029) (root 7) 2 2 :=
  of_native_maps core0029 DegreeOneMiddleResidualSpectrum076.graph DegreeOneMiddleResidualSpectrum041.graph
    sourceMap0029 fusedMap0029 sourceMap0029_checked fusedMap0029_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0029
#print axioms sourceMap0029_checked
#print axioms fusedMap0029_checked
#print axioms certified0029
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
