/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3080 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3080 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap3080 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap3080_checked : acceptsGraphIso
    (source (graph core3080) (root 4) 0 5) DegreeOneSmallSpectrum505.graph sourceMap3080=true := by decide +kernel
theorem fusedMap3080_checked : acceptsGraphIso
    (fused (graph core3080) (root 4) 0 5) DegreeOneSmallSpectrum379.graph fusedMap3080=true := by decide +kernel
theorem certified3080 : Certified (graph core3080) (root 4) 0 5 :=
  of_native_maps core3080 DegreeOneSmallSpectrum505.graph DegreeOneSmallSpectrum379.graph
    sourceMap3080 fusedMap3080 sourceMap3080_checked fusedMap3080_checked
    DegreeTwoThreeFiniteComparisons.comparison3080
#print axioms sourceMap3080_checked
#print axioms fusedMap3080_checked
#print axioms certified3080
def sourceMap3080swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,7] (sourceLabel 4 5 0 v)
def fusedMap3080swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap3080swap_checked : acceptsGraphIso
    (source (graph core3080) (root 4) 5 0) DegreeOneSmallSpectrum505.graph sourceMap3080swap=true := by decide +kernel
theorem fusedMap3080swap_checked : acceptsGraphIso
    (fused (graph core3080) (root 4) 5 0) DegreeOneSmallSpectrum379.graph fusedMap3080swap=true := by decide +kernel
theorem certified3080swap : Certified (graph core3080) (root 4) 5 0 :=
  of_native_maps core3080 DegreeOneSmallSpectrum505.graph DegreeOneSmallSpectrum379.graph
    sourceMap3080swap fusedMap3080swap sourceMap3080swap_checked fusedMap3080swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3080
#print axioms sourceMap3080swap_checked
#print axioms fusedMap3080swap_checked
#print axioms certified3080swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
