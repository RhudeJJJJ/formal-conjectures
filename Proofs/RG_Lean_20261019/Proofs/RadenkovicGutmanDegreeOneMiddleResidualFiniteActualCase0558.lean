/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0558 : Family 10 := level10.get ⟨93,by decide⟩
def sourceMap0558 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0558 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0558_checked : acceptsGraphIso
    (source (graph core0558) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1762.graph sourceMap0558=true := by decide +kernel
theorem fusedMap0558_checked : acceptsGraphIso
    (fused (graph core0558) (root 10) 2 2) DegreeOneMiddleResidualSpectrum975.graph fusedMap0558=true := by decide +kernel
theorem certified0558 : Certified (graph core0558) (root 10) 2 2 :=
  of_native_maps core0558 DegreeOneMiddleResidualSpectrum1762.graph DegreeOneMiddleResidualSpectrum975.graph
    sourceMap0558 fusedMap0558 sourceMap0558_checked fusedMap0558_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0558
#print axioms sourceMap0558_checked
#print axioms fusedMap0558_checked
#print axioms certified0558
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
