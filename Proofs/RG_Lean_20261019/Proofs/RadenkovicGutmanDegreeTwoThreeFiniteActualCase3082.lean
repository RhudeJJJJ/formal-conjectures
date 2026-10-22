/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3082 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3082 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3082 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3082_checked : acceptsGraphIso
    (source (graph core3082) (root 5) 0 5) DegreeOneSmallSpectrum881.graph sourceMap3082=true := by decide +kernel
theorem fusedMap3082_checked : acceptsGraphIso
    (fused (graph core3082) (root 5) 0 5) DegreeOneSmallSpectrum887.graph fusedMap3082=true := by decide +kernel
theorem certified3082 : Certified (graph core3082) (root 5) 0 5 :=
  of_native_maps core3082 DegreeOneSmallSpectrum881.graph DegreeOneSmallSpectrum887.graph
    sourceMap3082 fusedMap3082 sourceMap3082_checked fusedMap3082_checked
    DegreeTwoThreeFiniteComparisons.comparison3082
#print axioms sourceMap3082_checked
#print axioms fusedMap3082_checked
#print axioms certified3082
def sourceMap3082swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap3082swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3082swap_checked : acceptsGraphIso
    (source (graph core3082) (root 5) 5 0) DegreeOneSmallSpectrum881.graph sourceMap3082swap=true := by decide +kernel
theorem fusedMap3082swap_checked : acceptsGraphIso
    (fused (graph core3082) (root 5) 5 0) DegreeOneSmallSpectrum887.graph fusedMap3082swap=true := by decide +kernel
theorem certified3082swap : Certified (graph core3082) (root 5) 5 0 :=
  of_native_maps core3082 DegreeOneSmallSpectrum881.graph DegreeOneSmallSpectrum887.graph
    sourceMap3082swap fusedMap3082swap sourceMap3082swap_checked fusedMap3082swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3082
#print axioms sourceMap3082swap_checked
#print axioms fusedMap3082swap_checked
#print axioms certified3082swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
