/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0529 : Family 10 := level10.get ⟨55,by decide⟩
def sourceMap0529 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0529 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0529_checked : acceptsGraphIso
    (source (graph core0529) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1584.graph sourceMap0529=true := by decide +kernel
theorem fusedMap0529_checked : acceptsGraphIso
    (fused (graph core0529) (root 10) 2 2) DegreeTwoThreeSpectrum4967.graph fusedMap0529=true := by decide +kernel
theorem certified0529 : Certified (graph core0529) (root 10) 2 2 :=
  of_native_maps core0529 DegreeOneMiddleResidualSpectrum1584.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap0529 fusedMap0529 sourceMap0529_checked fusedMap0529_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0529
#print axioms sourceMap0529_checked
#print axioms fusedMap0529_checked
#print axioms certified0529
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
