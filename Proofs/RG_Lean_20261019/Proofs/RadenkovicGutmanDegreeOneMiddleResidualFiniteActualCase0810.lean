/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0810 : Family 10 := level10.get ⟨508,by decide⟩
def sourceMap0810 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0810 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0810_checked : acceptsGraphIso
    (source (graph core0810) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1985.graph sourceMap0810=true := by decide +kernel
theorem fusedMap0810_checked : acceptsGraphIso
    (fused (graph core0810) (root 10) 2 2) DegreeTwoThreeSpectrum5146.graph fusedMap0810=true := by decide +kernel
theorem certified0810 : Certified (graph core0810) (root 10) 2 2 :=
  of_native_maps core0810 DegreeOneMiddleResidualSpectrum1985.graph DegreeTwoThreeSpectrum5146.graph
    sourceMap0810 fusedMap0810 sourceMap0810_checked fusedMap0810_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0810
#print axioms sourceMap0810_checked
#print axioms fusedMap0810_checked
#print axioms certified0810
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
