/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1764 : Family 9 := level9.get ⟨649,by decide⟩
def sourceMap1764 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1764 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1764_checked : acceptsGraphIso
    (source (graph core1764) (root 9) 0 1) DegreeOneSmallSpectrum1933.graph sourceMap1764=true := by decide +kernel
theorem fusedMap1764_checked : acceptsGraphIso
    (fused (graph core1764) (root 9) 0 1) DegreeOneSmallSpectrum1934.graph fusedMap1764=true := by decide +kernel
theorem certified1764 : Certified (graph core1764) (root 9) 0 1 :=
  of_native_maps core1764 DegreeOneSmallSpectrum1933.graph DegreeOneSmallSpectrum1934.graph
    sourceMap1764 fusedMap1764 sourceMap1764_checked fusedMap1764_checked
    DegreeOneSmallComparisons.comparison1764
#print axioms sourceMap1764_checked
#print axioms fusedMap1764_checked
#print axioms certified1764
def sourceMap1764swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1764swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1764swap_checked : acceptsGraphIso
    (source (graph core1764) (root 9) 1 0) DegreeOneSmallSpectrum1933.graph sourceMap1764swap=true := by decide +kernel
theorem fusedMap1764swap_checked : acceptsGraphIso
    (fused (graph core1764) (root 9) 1 0) DegreeOneSmallSpectrum1934.graph fusedMap1764swap=true := by decide +kernel
theorem certified1764swap : Certified (graph core1764) (root 9) 1 0 :=
  of_native_maps core1764 DegreeOneSmallSpectrum1933.graph DegreeOneSmallSpectrum1934.graph
    sourceMap1764swap fusedMap1764swap sourceMap1764swap_checked fusedMap1764swap_checked
    DegreeOneSmallComparisons.comparison1764
#print axioms sourceMap1764swap_checked
#print axioms fusedMap1764swap_checked
#print axioms certified1764swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
