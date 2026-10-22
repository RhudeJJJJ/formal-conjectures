/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0988 : Family 10 := level10.get ⟨859,by decide⟩
def sourceMap0988 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0988 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0988_checked : acceptsGraphIso
    (source (graph core0988) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2290.graph sourceMap0988=true := by decide +kernel
theorem fusedMap0988_checked : acceptsGraphIso
    (fused (graph core0988) (root 10) 2 2) DegreeTwoThreeSpectrum5695.graph fusedMap0988=true := by decide +kernel
theorem certified0988 : Certified (graph core0988) (root 10) 2 2 :=
  of_native_maps core0988 DegreeOneMiddleResidualSpectrum2290.graph DegreeTwoThreeSpectrum5695.graph
    sourceMap0988 fusedMap0988 sourceMap0988_checked fusedMap0988_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0988
#print axioms sourceMap0988_checked
#print axioms fusedMap0988_checked
#print axioms certified0988
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
