/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0496 : Family 10 := level10.get ⟨13,by decide⟩
def sourceMap0496 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0496 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0496_checked : acceptsGraphIso
    (source (graph core0496) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1223.graph sourceMap0496=true := by decide +kernel
theorem fusedMap0496_checked : acceptsGraphIso
    (fused (graph core0496) (root 10) 2 2) DegreeTwoThreeSpectrum4993.graph fusedMap0496=true := by decide +kernel
theorem certified0496 : Certified (graph core0496) (root 10) 2 2 :=
  of_native_maps core0496 DegreeOneMiddleResidualSpectrum1223.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap0496 fusedMap0496 sourceMap0496_checked fusedMap0496_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0496
#print axioms sourceMap0496_checked
#print axioms fusedMap0496_checked
#print axioms certified0496
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
