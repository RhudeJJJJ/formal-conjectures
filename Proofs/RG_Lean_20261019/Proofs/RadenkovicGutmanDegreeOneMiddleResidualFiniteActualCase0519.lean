/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0519 : Family 10 := level10.get ⟨40,by decide⟩
def sourceMap0519 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0519 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0519_checked : acceptsGraphIso
    (source (graph core0519) (root 10) 2 2) DegreeTwoThreeSpectrum5669.graph sourceMap0519=true := by decide +kernel
theorem fusedMap0519_checked : acceptsGraphIso
    (fused (graph core0519) (root 10) 2 2) DegreeTwoThreeSpectrum5115.graph fusedMap0519=true := by decide +kernel
theorem certified0519 : Certified (graph core0519) (root 10) 2 2 :=
  of_native_maps core0519 DegreeTwoThreeSpectrum5669.graph DegreeTwoThreeSpectrum5115.graph
    sourceMap0519 fusedMap0519 sourceMap0519_checked fusedMap0519_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0519
#print axioms sourceMap0519_checked
#print axioms fusedMap0519_checked
#print axioms certified0519
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
