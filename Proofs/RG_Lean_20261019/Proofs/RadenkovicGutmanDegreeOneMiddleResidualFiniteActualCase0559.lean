/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0559 : Family 10 := level10.get ⟨94,by decide⟩
def sourceMap0559 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0559 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0559_checked : acceptsGraphIso
    (source (graph core0559) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1774.graph sourceMap0559=true := by decide +kernel
theorem fusedMap0559_checked : acceptsGraphIso
    (fused (graph core0559) (root 10) 2 2) DegreeTwoThreeSpectrum5015.graph fusedMap0559=true := by decide +kernel
theorem certified0559 : Certified (graph core0559) (root 10) 2 2 :=
  of_native_maps core0559 DegreeOneMiddleResidualSpectrum1774.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap0559 fusedMap0559 sourceMap0559_checked fusedMap0559_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0559
#print axioms sourceMap0559_checked
#print axioms fusedMap0559_checked
#print axioms certified0559
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
