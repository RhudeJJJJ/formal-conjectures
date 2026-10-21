/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1614 : Family 9 := level9.get ⟨357,by decide⟩
def sourceMap1614 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1614 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1614_checked : acceptsGraphIso
    (source (graph core1614) (root 9) 0 1) DegreeOneSmallSpectrum1732.graph sourceMap1614=true := by decide +kernel
theorem fusedMap1614_checked : acceptsGraphIso
    (fused (graph core1614) (root 9) 0 1) DegreeOneSmallSpectrum1089.graph fusedMap1614=true := by decide +kernel
theorem certified1614 : Certified (graph core1614) (root 9) 0 1 :=
  of_native_maps core1614 DegreeOneSmallSpectrum1732.graph DegreeOneSmallSpectrum1089.graph
    sourceMap1614 fusedMap1614 sourceMap1614_checked fusedMap1614_checked
    DegreeOneSmallComparisons.comparison1614
#print axioms sourceMap1614_checked
#print axioms fusedMap1614_checked
#print axioms certified1614
def sourceMap1614swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1614swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1614swap_checked : acceptsGraphIso
    (source (graph core1614) (root 9) 1 0) DegreeOneSmallSpectrum1732.graph sourceMap1614swap=true := by decide +kernel
theorem fusedMap1614swap_checked : acceptsGraphIso
    (fused (graph core1614) (root 9) 1 0) DegreeOneSmallSpectrum1089.graph fusedMap1614swap=true := by decide +kernel
theorem certified1614swap : Certified (graph core1614) (root 9) 1 0 :=
  of_native_maps core1614 DegreeOneSmallSpectrum1732.graph DegreeOneSmallSpectrum1089.graph
    sourceMap1614swap fusedMap1614swap sourceMap1614swap_checked fusedMap1614swap_checked
    DegreeOneSmallComparisons.comparison1614
#print axioms sourceMap1614swap_checked
#print axioms fusedMap1614swap_checked
#print axioms certified1614swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
