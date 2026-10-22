/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0145 : Family 8 := level8.get ⟨141,by decide⟩
def sourceMap0145 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0145 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0145_checked : acceptsGraphIso
    (source (graph core0145) (root 8) 2 2) DegreeOneMiddleResidualSpectrum307.graph sourceMap0145=true := by decide +kernel
theorem fusedMap0145_checked : acceptsGraphIso
    (fused (graph core0145) (root 8) 2 2) DegreeOneMiddleResidualSpectrum218.graph fusedMap0145=true := by decide +kernel
theorem certified0145 : Certified (graph core0145) (root 8) 2 2 :=
  of_native_maps core0145 DegreeOneMiddleResidualSpectrum307.graph DegreeOneMiddleResidualSpectrum218.graph
    sourceMap0145 fusedMap0145 sourceMap0145_checked fusedMap0145_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0145
#print axioms sourceMap0145_checked
#print axioms fusedMap0145_checked
#print axioms certified0145
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
