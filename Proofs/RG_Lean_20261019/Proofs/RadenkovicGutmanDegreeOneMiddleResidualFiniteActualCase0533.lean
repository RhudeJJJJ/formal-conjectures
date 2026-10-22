/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0533 : Family 10 := level10.get ⟨60,by decide⟩
def sourceMap0533 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0533 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0533_checked : acceptsGraphIso
    (source (graph core0533) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1619.graph sourceMap0533=true := by decide +kernel
theorem fusedMap0533_checked : acceptsGraphIso
    (fused (graph core0533) (root 10) 2 2) DegreeTwoThreeSpectrum4973.graph fusedMap0533=true := by decide +kernel
theorem certified0533 : Certified (graph core0533) (root 10) 2 2 :=
  of_native_maps core0533 DegreeOneMiddleResidualSpectrum1619.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap0533 fusedMap0533 sourceMap0533_checked fusedMap0533_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0533
#print axioms sourceMap0533_checked
#print axioms fusedMap0533_checked
#print axioms certified0533
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
