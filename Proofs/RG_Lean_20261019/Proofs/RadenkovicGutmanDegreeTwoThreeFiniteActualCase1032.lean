/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1032 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap1032 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 3) → Fin 7 :=
  fun v => ![1,2,3,4,0,5,6] (sourceLabel 2 0 2 v)
def fusedMap1032 : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 0 2 v)
theorem sourceMap1032_checked : acceptsGraphIso
    (source (graph core1032) (root 2) 0 2) DegreeOneSmallSpectrum012.graph sourceMap1032=true := by decide +kernel
theorem fusedMap1032_checked : acceptsGraphIso
    (fused (graph core1032) (root 2) 0 2) DegreeOneSmallSpectrum008.graph fusedMap1032=true := by decide +kernel
theorem certified1032 : Certified (graph core1032) (root 2) 0 2 :=
  of_native_maps core1032 DegreeOneSmallSpectrum012.graph DegreeOneSmallSpectrum008.graph
    sourceMap1032 fusedMap1032 sourceMap1032_checked fusedMap1032_checked
    DegreeTwoThreeFiniteComparisons.comparison1032
#print axioms sourceMap1032_checked
#print axioms fusedMap1032_checked
#print axioms certified1032
def sourceMap1032swap : (Vertices 2 ⊕ Fin 3 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,2,3,0,5,6,4] (sourceLabel 2 2 0 v)
def fusedMap1032swap : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 2 0 v)
theorem sourceMap1032swap_checked : acceptsGraphIso
    (source (graph core1032) (root 2) 2 0) DegreeOneSmallSpectrum012.graph sourceMap1032swap=true := by decide +kernel
theorem fusedMap1032swap_checked : acceptsGraphIso
    (fused (graph core1032) (root 2) 2 0) DegreeOneSmallSpectrum008.graph fusedMap1032swap=true := by decide +kernel
theorem certified1032swap : Certified (graph core1032) (root 2) 2 0 :=
  of_native_maps core1032 DegreeOneSmallSpectrum012.graph DegreeOneSmallSpectrum008.graph
    sourceMap1032swap fusedMap1032swap sourceMap1032swap_checked fusedMap1032swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1032
#print axioms sourceMap1032swap_checked
#print axioms fusedMap1032swap_checked
#print axioms certified1032swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
