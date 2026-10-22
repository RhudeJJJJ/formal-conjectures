/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0671 : Family 10 := level10.get ⟨259,by decide⟩
def sourceMap0671 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0671 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0671_checked : acceptsGraphIso
    (source (graph core0671) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1686.graph sourceMap0671=true := by decide +kernel
theorem fusedMap0671_checked : acceptsGraphIso
    (fused (graph core0671) (root 10) 2 2) DegreeTwoThreeSpectrum5367.graph fusedMap0671=true := by decide +kernel
theorem certified0671 : Certified (graph core0671) (root 10) 2 2 :=
  of_native_maps core0671 DegreeOneMiddleResidualSpectrum1686.graph DegreeTwoThreeSpectrum5367.graph
    sourceMap0671 fusedMap0671 sourceMap0671_checked fusedMap0671_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0671
#print axioms sourceMap0671_checked
#print axioms fusedMap0671_checked
#print axioms certified0671
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
