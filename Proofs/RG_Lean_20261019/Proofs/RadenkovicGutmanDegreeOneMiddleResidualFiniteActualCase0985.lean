/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0985 : Family 10 := level10.get ⟨855,by decide⟩
def sourceMap0985 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0985 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0985_checked : acceptsGraphIso
    (source (graph core0985) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2287.graph sourceMap0985=true := by decide +kernel
theorem fusedMap0985_checked : acceptsGraphIso
    (fused (graph core0985) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1408.graph fusedMap0985=true := by decide +kernel
theorem certified0985 : Certified (graph core0985) (root 10) 2 2 :=
  of_native_maps core0985 DegreeOneMiddleResidualSpectrum2287.graph DegreeOneMiddleResidualSpectrum1408.graph
    sourceMap0985 fusedMap0985 sourceMap0985_checked fusedMap0985_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0985
#print axioms sourceMap0985_checked
#print axioms fusedMap0985_checked
#print axioms certified0985
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
