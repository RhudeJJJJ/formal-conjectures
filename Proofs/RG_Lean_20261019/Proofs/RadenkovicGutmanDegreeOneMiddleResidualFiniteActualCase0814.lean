/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0814 : Family 10 := level10.get ⟨516,by decide⟩
def sourceMap0814 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0814 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0814_checked : acceptsGraphIso
    (source (graph core0814) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1992.graph sourceMap0814=true := by decide +kernel
theorem fusedMap0814_checked : acceptsGraphIso
    (fused (graph core0814) (root 10) 2 2) DegreeTwoThreeSpectrum5159.graph fusedMap0814=true := by decide +kernel
theorem certified0814 : Certified (graph core0814) (root 10) 2 2 :=
  of_native_maps core0814 DegreeOneMiddleResidualSpectrum1992.graph DegreeTwoThreeSpectrum5159.graph
    sourceMap0814 fusedMap0814 sourceMap0814_checked fusedMap0814_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0814
#print axioms sourceMap0814_checked
#print axioms fusedMap0814_checked
#print axioms certified0814
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
