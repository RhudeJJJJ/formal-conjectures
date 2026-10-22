/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0627 : Family 10 := level10.get ⟨774,by decide⟩
def sourceMap0627 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0627 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0627_checked : acceptsGraphIso
    (source (graph core0627) (root 10) 0 0) DegreeOneSmallSpectrum1689.graph sourceMap0627=true := by decide +kernel
theorem fusedMap0627_checked : acceptsGraphIso
    (fused (graph core0627) (root 10) 0 0) DegreeOneSmallSpectrum1406.graph fusedMap0627=true := by decide +kernel
theorem certified0627 : Certified (graph core0627) (root 10) 0 0 :=
  of_native_maps core0627 DegreeOneSmallSpectrum1689.graph DegreeOneSmallSpectrum1406.graph
    sourceMap0627 fusedMap0627 sourceMap0627_checked fusedMap0627_checked
    DegreeTwoThreeFiniteComparisons.comparison0627
#print axioms sourceMap0627_checked
#print axioms fusedMap0627_checked
#print axioms certified0627
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
