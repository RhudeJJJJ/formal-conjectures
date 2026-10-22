/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1106 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap1106 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,11,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1106 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1106_checked : acceptsGraphIso
    (source (graph core1106) (root 8) 0 2) DegreeOneSmallSpectrum1285.graph sourceMap1106=true := by decide +kernel
theorem fusedMap1106_checked : acceptsGraphIso
    (fused (graph core1106) (root 8) 0 2) DegreeOneSmallSpectrum893.graph fusedMap1106=true := by decide +kernel
theorem certified1106 : Certified (graph core1106) (root 8) 0 2 :=
  of_native_maps core1106 DegreeOneSmallSpectrum1285.graph DegreeOneSmallSpectrum893.graph
    sourceMap1106 fusedMap1106 sourceMap1106_checked fusedMap1106_checked
    DegreeTwoThreeFiniteComparisons.comparison1106
#print axioms sourceMap1106_checked
#print axioms fusedMap1106_checked
#print axioms certified1106
def sourceMap1106swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,7,8,9,11] (sourceLabel 8 2 0 v)
def fusedMap1106swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1106swap_checked : acceptsGraphIso
    (source (graph core1106) (root 8) 2 0) DegreeOneSmallSpectrum1285.graph sourceMap1106swap=true := by decide +kernel
theorem fusedMap1106swap_checked : acceptsGraphIso
    (fused (graph core1106) (root 8) 2 0) DegreeOneSmallSpectrum893.graph fusedMap1106swap=true := by decide +kernel
theorem certified1106swap : Certified (graph core1106) (root 8) 2 0 :=
  of_native_maps core1106 DegreeOneSmallSpectrum1285.graph DegreeOneSmallSpectrum893.graph
    sourceMap1106swap fusedMap1106swap sourceMap1106swap_checked fusedMap1106swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1106
#print axioms sourceMap1106swap_checked
#print axioms fusedMap1106swap_checked
#print axioms certified1106swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
