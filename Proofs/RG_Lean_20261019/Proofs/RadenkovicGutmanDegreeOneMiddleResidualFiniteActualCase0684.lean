/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0684 : Family 10 := level10.get ⟨285,by decide⟩
def sourceMap0684 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0684 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0684_checked : acceptsGraphIso
    (source (graph core0684) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1720.graph sourceMap0684=true := by decide +kernel
theorem fusedMap0684_checked : acceptsGraphIso
    (fused (graph core0684) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1239.graph fusedMap0684=true := by decide +kernel
theorem certified0684 : Certified (graph core0684) (root 10) 2 2 :=
  of_native_maps core0684 DegreeOneMiddleResidualSpectrum1720.graph DegreeOneMiddleResidualSpectrum1239.graph
    sourceMap0684 fusedMap0684 sourceMap0684_checked fusedMap0684_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0684
#print axioms sourceMap0684_checked
#print axioms fusedMap0684_checked
#print axioms certified0684
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
