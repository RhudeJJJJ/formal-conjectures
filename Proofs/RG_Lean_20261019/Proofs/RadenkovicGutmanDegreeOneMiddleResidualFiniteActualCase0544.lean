/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0544 : Family 10 := level10.get ⟨73,by decide⟩
def sourceMap0544 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0544 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0544_checked : acceptsGraphIso
    (source (graph core0544) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1690.graph sourceMap0544=true := by decide +kernel
theorem fusedMap0544_checked : acceptsGraphIso
    (fused (graph core0544) (root 10) 2 2) DegreeTwoThreeSpectrum4988.graph fusedMap0544=true := by decide +kernel
theorem certified0544 : Certified (graph core0544) (root 10) 2 2 :=
  of_native_maps core0544 DegreeOneMiddleResidualSpectrum1690.graph DegreeTwoThreeSpectrum4988.graph
    sourceMap0544 fusedMap0544 sourceMap0544_checked fusedMap0544_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0544
#print axioms sourceMap0544_checked
#print axioms fusedMap0544_checked
#print axioms certified0544
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
