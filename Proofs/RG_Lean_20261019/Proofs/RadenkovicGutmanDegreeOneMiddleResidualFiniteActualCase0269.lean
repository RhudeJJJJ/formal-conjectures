/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0269 : Family 9 := level9.get ⟨94,by decide⟩
def sourceMap0269 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0269 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0269_checked : acceptsGraphIso
    (source (graph core0269) (root 9) 2 2) DegreeOneMiddleResidualSpectrum709.graph sourceMap0269=true := by decide +kernel
theorem fusedMap0269_checked : acceptsGraphIso
    (fused (graph core0269) (root 9) 2 2) DegreeTwoThreeSpectrum4067.graph fusedMap0269=true := by decide +kernel
theorem certified0269 : Certified (graph core0269) (root 9) 2 2 :=
  of_native_maps core0269 DegreeOneMiddleResidualSpectrum709.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap0269 fusedMap0269 sourceMap0269_checked fusedMap0269_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0269
#print axioms sourceMap0269_checked
#print axioms fusedMap0269_checked
#print axioms certified0269
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
