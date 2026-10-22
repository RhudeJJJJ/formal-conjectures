/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0531 : Family 10 := level10.get ⟨485,by decide⟩
def sourceMap0531 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0531 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0531_checked : acceptsGraphIso
    (source (graph core0531) (root 10) 0 0) DegreeOneSmallSpectrum1124.graph sourceMap0531=true := by decide +kernel
theorem fusedMap0531_checked : acceptsGraphIso
    (fused (graph core0531) (root 10) 0 0) DegreeOneSmallSpectrum1101.graph fusedMap0531=true := by decide +kernel
theorem certified0531 : Certified (graph core0531) (root 10) 0 0 :=
  of_native_maps core0531 DegreeOneSmallSpectrum1124.graph DegreeOneSmallSpectrum1101.graph
    sourceMap0531 fusedMap0531 sourceMap0531_checked fusedMap0531_checked
    DegreeTwoThreeFiniteComparisons.comparison0531
#print axioms sourceMap0531_checked
#print axioms fusedMap0531_checked
#print axioms certified0531
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
