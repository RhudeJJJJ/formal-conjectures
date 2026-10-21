/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1682 : Family 9 := level9.get ⟨442,by decide⟩
def sourceMap1682 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1682 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1682_checked : acceptsGraphIso
    (source (graph core1682) (root 9) 0 1) DegreeOneSmallSpectrum1941.graph sourceMap1682=true := by decide +kernel
theorem fusedMap1682_checked : acceptsGraphIso
    (fused (graph core1682) (root 9) 0 1) DegreeOneSmallSpectrum1355.graph fusedMap1682=true := by decide +kernel
theorem certified1682 : Certified (graph core1682) (root 9) 0 1 :=
  of_native_maps core1682 DegreeOneSmallSpectrum1941.graph DegreeOneSmallSpectrum1355.graph
    sourceMap1682 fusedMap1682 sourceMap1682_checked fusedMap1682_checked
    DegreeOneSmallComparisons.comparison1682
#print axioms sourceMap1682_checked
#print axioms fusedMap1682_checked
#print axioms certified1682
def sourceMap1682swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1682swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1682swap_checked : acceptsGraphIso
    (source (graph core1682) (root 9) 1 0) DegreeOneSmallSpectrum1941.graph sourceMap1682swap=true := by decide +kernel
theorem fusedMap1682swap_checked : acceptsGraphIso
    (fused (graph core1682) (root 9) 1 0) DegreeOneSmallSpectrum1355.graph fusedMap1682swap=true := by decide +kernel
theorem certified1682swap : Certified (graph core1682) (root 9) 1 0 :=
  of_native_maps core1682 DegreeOneSmallSpectrum1941.graph DegreeOneSmallSpectrum1355.graph
    sourceMap1682swap fusedMap1682swap sourceMap1682swap_checked fusedMap1682swap_checked
    DegreeOneSmallComparisons.comparison1682
#print axioms sourceMap1682swap_checked
#print axioms fusedMap1682swap_checked
#print axioms certified1682swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
