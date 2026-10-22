/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0590 : Family 10 := level10.get ⟨667,by decide⟩
def sourceMap0590 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0590 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0590_checked : acceptsGraphIso
    (source (graph core0590) (root 10) 0 0) DegreeOneSmallSpectrum1643.graph sourceMap0590=true := by decide +kernel
theorem fusedMap0590_checked : acceptsGraphIso
    (fused (graph core0590) (root 10) 0 0) DegreeOneSmallSpectrum1269.graph fusedMap0590=true := by decide +kernel
theorem certified0590 : Certified (graph core0590) (root 10) 0 0 :=
  of_native_maps core0590 DegreeOneSmallSpectrum1643.graph DegreeOneSmallSpectrum1269.graph
    sourceMap0590 fusedMap0590 sourceMap0590_checked fusedMap0590_checked
    DegreeTwoThreeFiniteComparisons.comparison0590
#print axioms sourceMap0590_checked
#print axioms fusedMap0590_checked
#print axioms certified0590
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
