/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0796 : Family 10 := level10.get ⟨472,by decide⟩
def sourceMap0796 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0796 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0796_checked : acceptsGraphIso
    (source (graph core0796) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1844.graph sourceMap0796=true := by decide +kernel
theorem fusedMap0796_checked : acceptsGraphIso
    (fused (graph core0796) (root 10) 2 2) DegreeTwoThreeSpectrum5930.graph fusedMap0796=true := by decide +kernel
theorem certified0796 : Certified (graph core0796) (root 10) 2 2 :=
  of_native_maps core0796 DegreeOneMiddleResidualSpectrum1844.graph DegreeTwoThreeSpectrum5930.graph
    sourceMap0796 fusedMap0796 sourceMap0796_checked fusedMap0796_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0796
#print axioms sourceMap0796_checked
#print axioms fusedMap0796_checked
#print axioms certified0796
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
