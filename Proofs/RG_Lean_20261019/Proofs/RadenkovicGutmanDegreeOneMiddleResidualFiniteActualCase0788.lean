/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0788 : Family 10 := level10.get ⟨455,by decide⟩
def sourceMap0788 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0788 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0788_checked : acceptsGraphIso
    (source (graph core0788) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1842.graph sourceMap0788=true := by decide +kernel
theorem fusedMap0788_checked : acceptsGraphIso
    (fused (graph core0788) (root 10) 2 2) DegreeTwoThreeSpectrum5889.graph fusedMap0788=true := by decide +kernel
theorem certified0788 : Certified (graph core0788) (root 10) 2 2 :=
  of_native_maps core0788 DegreeOneMiddleResidualSpectrum1842.graph DegreeTwoThreeSpectrum5889.graph
    sourceMap0788 fusedMap0788 sourceMap0788_checked fusedMap0788_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0788
#print axioms sourceMap0788_checked
#print axioms fusedMap0788_checked
#print axioms certified0788
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
