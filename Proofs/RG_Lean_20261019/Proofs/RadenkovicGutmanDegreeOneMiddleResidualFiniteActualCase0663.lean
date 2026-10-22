/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0663 : Family 10 := level10.get ⟨246,by decide⟩
def sourceMap0663 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0663 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0663_checked : acceptsGraphIso
    (source (graph core0663) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1674.graph sourceMap0663=true := by decide +kernel
theorem fusedMap0663_checked : acceptsGraphIso
    (fused (graph core0663) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1191.graph fusedMap0663=true := by decide +kernel
theorem certified0663 : Certified (graph core0663) (root 10) 2 2 :=
  of_native_maps core0663 DegreeOneMiddleResidualSpectrum1674.graph DegreeOneMiddleResidualSpectrum1191.graph
    sourceMap0663 fusedMap0663 sourceMap0663_checked fusedMap0663_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0663
#print axioms sourceMap0663_checked
#print axioms fusedMap0663_checked
#print axioms certified0663
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
