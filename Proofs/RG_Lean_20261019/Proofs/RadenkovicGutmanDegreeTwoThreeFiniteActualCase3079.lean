/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3079 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3079 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap3079 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap3079_checked : acceptsGraphIso
    (source (graph core3079) (root 4) 0 5) DegreeOneSmallSpectrum440.graph sourceMap3079=true := by decide +kernel
theorem fusedMap3079_checked : acceptsGraphIso
    (fused (graph core3079) (root 4) 0 5) DegreeOneSmallSpectrum371.graph fusedMap3079=true := by decide +kernel
theorem certified3079 : Certified (graph core3079) (root 4) 0 5 :=
  of_native_maps core3079 DegreeOneSmallSpectrum440.graph DegreeOneSmallSpectrum371.graph
    sourceMap3079 fusedMap3079 sourceMap3079_checked fusedMap3079_checked
    DegreeTwoThreeFiniteComparisons.comparison3079
#print axioms sourceMap3079_checked
#print axioms fusedMap3079_checked
#print axioms certified3079
def sourceMap3079swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,7] (sourceLabel 4 5 0 v)
def fusedMap3079swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap3079swap_checked : acceptsGraphIso
    (source (graph core3079) (root 4) 5 0) DegreeOneSmallSpectrum440.graph sourceMap3079swap=true := by decide +kernel
theorem fusedMap3079swap_checked : acceptsGraphIso
    (fused (graph core3079) (root 4) 5 0) DegreeOneSmallSpectrum371.graph fusedMap3079swap=true := by decide +kernel
theorem certified3079swap : Certified (graph core3079) (root 4) 5 0 :=
  of_native_maps core3079 DegreeOneSmallSpectrum440.graph DegreeOneSmallSpectrum371.graph
    sourceMap3079swap fusedMap3079swap sourceMap3079swap_checked fusedMap3079swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3079
#print axioms sourceMap3079swap_checked
#print axioms fusedMap3079swap_checked
#print axioms certified3079swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
