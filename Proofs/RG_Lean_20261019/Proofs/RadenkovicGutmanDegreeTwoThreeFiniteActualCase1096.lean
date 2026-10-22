/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1096 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap1096 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap1096 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap1096_checked : acceptsGraphIso
    (source (graph core1096) (root 8) 0 2) DegreeOneSmallSpectrum956.graph sourceMap1096=true := by decide +kernel
theorem fusedMap1096_checked : acceptsGraphIso
    (fused (graph core1096) (root 8) 0 2) DegreeOneSmallSpectrum859.graph fusedMap1096=true := by decide +kernel
theorem certified1096 : Certified (graph core1096) (root 8) 0 2 :=
  of_native_maps core1096 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum859.graph
    sourceMap1096 fusedMap1096 sourceMap1096_checked fusedMap1096_checked
    DegreeTwoThreeFiniteComparisons.comparison1096
#print axioms sourceMap1096_checked
#print axioms fusedMap1096_checked
#print axioms certified1096
def sourceMap1096swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,3,4,5,7] (sourceLabel 8 2 0 v)
def fusedMap1096swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap1096swap_checked : acceptsGraphIso
    (source (graph core1096) (root 8) 2 0) DegreeOneSmallSpectrum956.graph sourceMap1096swap=true := by decide +kernel
theorem fusedMap1096swap_checked : acceptsGraphIso
    (fused (graph core1096) (root 8) 2 0) DegreeOneSmallSpectrum859.graph fusedMap1096swap=true := by decide +kernel
theorem certified1096swap : Certified (graph core1096) (root 8) 2 0 :=
  of_native_maps core1096 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum859.graph
    sourceMap1096swap fusedMap1096swap sourceMap1096swap_checked fusedMap1096swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1096
#print axioms sourceMap1096swap_checked
#print axioms fusedMap1096swap_checked
#print axioms certified1096swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
