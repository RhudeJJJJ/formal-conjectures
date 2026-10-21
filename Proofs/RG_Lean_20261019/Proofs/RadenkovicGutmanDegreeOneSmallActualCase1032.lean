/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1032 : Family 8 := level8.get ⟨113,by decide⟩
def sourceMap1032 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap1032 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1032_checked : acceptsGraphIso
    (source (graph core1032) (root 8) 0 1) DegreeOneSmallSpectrum726.graph sourceMap1032=true := by decide +kernel
theorem fusedMap1032_checked : acceptsGraphIso
    (fused (graph core1032) (root 8) 0 1) DegreeOneSmallSpectrum436.graph fusedMap1032=true := by decide +kernel
theorem certified1032 : Certified (graph core1032) (root 8) 0 1 :=
  of_native_maps core1032 DegreeOneSmallSpectrum726.graph DegreeOneSmallSpectrum436.graph
    sourceMap1032 fusedMap1032 sourceMap1032_checked fusedMap1032_checked
    DegreeOneSmallComparisons.comparison1032
#print axioms sourceMap1032_checked
#print axioms fusedMap1032_checked
#print axioms certified1032
def sourceMap1032swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap1032swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1032swap_checked : acceptsGraphIso
    (source (graph core1032) (root 8) 1 0) DegreeOneSmallSpectrum726.graph sourceMap1032swap=true := by decide +kernel
theorem fusedMap1032swap_checked : acceptsGraphIso
    (fused (graph core1032) (root 8) 1 0) DegreeOneSmallSpectrum436.graph fusedMap1032swap=true := by decide +kernel
theorem certified1032swap : Certified (graph core1032) (root 8) 1 0 :=
  of_native_maps core1032 DegreeOneSmallSpectrum726.graph DegreeOneSmallSpectrum436.graph
    sourceMap1032swap fusedMap1032swap sourceMap1032swap_checked fusedMap1032swap_checked
    DegreeOneSmallComparisons.comparison1032
#print axioms sourceMap1032swap_checked
#print axioms fusedMap1032swap_checked
#print axioms certified1032swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
