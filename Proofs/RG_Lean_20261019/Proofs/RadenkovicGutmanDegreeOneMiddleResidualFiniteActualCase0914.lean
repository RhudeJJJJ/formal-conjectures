/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0914 : Family 10 := level10.get ⟨705,by decide⟩
def sourceMap0914 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0914 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0914_checked : acceptsGraphIso
    (source (graph core0914) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2177.graph sourceMap0914=true := by decide +kernel
theorem fusedMap0914_checked : acceptsGraphIso
    (fused (graph core0914) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1253.graph fusedMap0914=true := by decide +kernel
theorem certified0914 : Certified (graph core0914) (root 10) 2 2 :=
  of_native_maps core0914 DegreeOneMiddleResidualSpectrum2177.graph DegreeOneMiddleResidualSpectrum1253.graph
    sourceMap0914 fusedMap0914 sourceMap0914_checked fusedMap0914_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0914
#print axioms sourceMap0914_checked
#print axioms fusedMap0914_checked
#print axioms certified0914
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
