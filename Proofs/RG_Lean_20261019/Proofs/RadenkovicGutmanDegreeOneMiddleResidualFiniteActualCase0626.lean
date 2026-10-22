/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0626 : Family 10 := level10.get ⟨195,by decide⟩
def sourceMap0626 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0626 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0626_checked : acceptsGraphIso
    (source (graph core0626) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1557.graph sourceMap0626=true := by decide +kernel
theorem fusedMap0626_checked : acceptsGraphIso
    (fused (graph core0626) (root 10) 2 2) DegreeTwoThreeSpectrum5164.graph fusedMap0626=true := by decide +kernel
theorem certified0626 : Certified (graph core0626) (root 10) 2 2 :=
  of_native_maps core0626 DegreeOneMiddleResidualSpectrum1557.graph DegreeTwoThreeSpectrum5164.graph
    sourceMap0626 fusedMap0626 sourceMap0626_checked fusedMap0626_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0626
#print axioms sourceMap0626_checked
#print axioms fusedMap0626_checked
#print axioms certified0626
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
