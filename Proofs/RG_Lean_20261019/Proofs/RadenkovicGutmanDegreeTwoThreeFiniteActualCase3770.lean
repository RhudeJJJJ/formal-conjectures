/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3770 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3770 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,6,7,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap3770 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap3770_checked : acceptsGraphIso
    (source (graph core3770) (root 5) 1 4) DegreeOneSmallSpectrum1408.graph sourceMap3770=true := by decide +kernel
theorem fusedMap3770_checked : acceptsGraphIso
    (fused (graph core3770) (root 5) 1 4) DegreeOneSmallSpectrum929.graph fusedMap3770=true := by decide +kernel
theorem certified3770 : Certified (graph core3770) (root 5) 1 4 :=
  of_native_maps core3770 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum929.graph
    sourceMap3770 fusedMap3770 sourceMap3770_checked fusedMap3770_checked
    DegreeTwoThreeFiniteComparisons.comparison3770
#print axioms sourceMap3770_checked
#print axioms fusedMap3770_checked
#print axioms certified3770
def sourceMap3770swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,8,0,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap3770swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap3770swap_checked : acceptsGraphIso
    (source (graph core3770) (root 5) 4 1) DegreeOneSmallSpectrum1408.graph sourceMap3770swap=true := by decide +kernel
theorem fusedMap3770swap_checked : acceptsGraphIso
    (fused (graph core3770) (root 5) 4 1) DegreeOneSmallSpectrum929.graph fusedMap3770swap=true := by decide +kernel
theorem certified3770swap : Certified (graph core3770) (root 5) 4 1 :=
  of_native_maps core3770 DegreeOneSmallSpectrum1408.graph DegreeOneSmallSpectrum929.graph
    sourceMap3770swap fusedMap3770swap sourceMap3770swap_checked fusedMap3770swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3770
#print axioms sourceMap3770swap_checked
#print axioms fusedMap3770swap_checked
#print axioms certified3770swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
