/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1320 : Family 9 := level9.get ⟨80,by decide⟩
def sourceMap1320 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1320 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1320_checked : acceptsGraphIso
    (source (graph core1320) (root 9) 0 1) DegreeOneSmallSpectrum1420.graph sourceMap1320=true := by decide +kernel
theorem fusedMap1320_checked : acceptsGraphIso
    (fused (graph core1320) (root 9) 0 1) DegreeOneSmallSpectrum924.graph fusedMap1320=true := by decide +kernel
theorem certified1320 : Certified (graph core1320) (root 9) 0 1 :=
  of_native_maps core1320 DegreeOneSmallSpectrum1420.graph DegreeOneSmallSpectrum924.graph
    sourceMap1320 fusedMap1320 sourceMap1320_checked fusedMap1320_checked
    DegreeOneSmallComparisons.comparison1320
#print axioms sourceMap1320_checked
#print axioms fusedMap1320_checked
#print axioms certified1320
def sourceMap1320swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1320swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1320swap_checked : acceptsGraphIso
    (source (graph core1320) (root 9) 1 0) DegreeOneSmallSpectrum1420.graph sourceMap1320swap=true := by decide +kernel
theorem fusedMap1320swap_checked : acceptsGraphIso
    (fused (graph core1320) (root 9) 1 0) DegreeOneSmallSpectrum924.graph fusedMap1320swap=true := by decide +kernel
theorem certified1320swap : Certified (graph core1320) (root 9) 1 0 :=
  of_native_maps core1320 DegreeOneSmallSpectrum1420.graph DegreeOneSmallSpectrum924.graph
    sourceMap1320swap fusedMap1320swap sourceMap1320swap_checked fusedMap1320swap_checked
    DegreeOneSmallComparisons.comparison1320
#print axioms sourceMap1320swap_checked
#print axioms fusedMap1320swap_checked
#print axioms certified1320swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
