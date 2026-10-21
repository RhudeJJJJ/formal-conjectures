/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1700 : Family 9 := level9.get ⟨464,by decide⟩
def sourceMap1700 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1700 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1700_checked : acceptsGraphIso
    (source (graph core1700) (root 9) 0 1) DegreeOneSmallSpectrum1960.graph sourceMap1700=true := by decide +kernel
theorem fusedMap1700_checked : acceptsGraphIso
    (fused (graph core1700) (root 9) 0 1) DegreeOneSmallSpectrum1404.graph fusedMap1700=true := by decide +kernel
theorem certified1700 : Certified (graph core1700) (root 9) 0 1 :=
  of_native_maps core1700 DegreeOneSmallSpectrum1960.graph DegreeOneSmallSpectrum1404.graph
    sourceMap1700 fusedMap1700 sourceMap1700_checked fusedMap1700_checked
    DegreeOneSmallComparisons.comparison1700
#print axioms sourceMap1700_checked
#print axioms fusedMap1700_checked
#print axioms certified1700
def sourceMap1700swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1700swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1700swap_checked : acceptsGraphIso
    (source (graph core1700) (root 9) 1 0) DegreeOneSmallSpectrum1960.graph sourceMap1700swap=true := by decide +kernel
theorem fusedMap1700swap_checked : acceptsGraphIso
    (fused (graph core1700) (root 9) 1 0) DegreeOneSmallSpectrum1404.graph fusedMap1700swap=true := by decide +kernel
theorem certified1700swap : Certified (graph core1700) (root 9) 1 0 :=
  of_native_maps core1700 DegreeOneSmallSpectrum1960.graph DegreeOneSmallSpectrum1404.graph
    sourceMap1700swap fusedMap1700swap sourceMap1700swap_checked fusedMap1700swap_checked
    DegreeOneSmallComparisons.comparison1700
#print axioms sourceMap1700swap_checked
#print axioms fusedMap1700swap_checked
#print axioms certified1700swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
