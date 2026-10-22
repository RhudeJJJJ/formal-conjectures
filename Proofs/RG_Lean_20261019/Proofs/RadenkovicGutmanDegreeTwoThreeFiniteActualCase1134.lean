/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1134 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap1134 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 8 0 2 v)
def fusedMap1134 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1134_checked : acceptsGraphIso
    (source (graph core1134) (root 8) 0 2) DegreeOneSmallSpectrum1277.graph sourceMap1134=true := by decide +kernel
theorem fusedMap1134_checked : acceptsGraphIso
    (fused (graph core1134) (root 8) 0 2) DegreeOneSmallSpectrum1289.graph fusedMap1134=true := by decide +kernel
theorem certified1134 : Certified (graph core1134) (root 8) 0 2 :=
  of_native_maps core1134 DegreeOneSmallSpectrum1277.graph DegreeOneSmallSpectrum1289.graph
    sourceMap1134 fusedMap1134 sourceMap1134_checked fusedMap1134_checked
    DegreeTwoThreeFiniteComparisons.comparison1134
#print axioms sourceMap1134_checked
#print axioms fusedMap1134_checked
#print axioms certified1134
def sourceMap1134swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8,12] (sourceLabel 8 2 0 v)
def fusedMap1134swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1134swap_checked : acceptsGraphIso
    (source (graph core1134) (root 8) 2 0) DegreeOneSmallSpectrum1277.graph sourceMap1134swap=true := by decide +kernel
theorem fusedMap1134swap_checked : acceptsGraphIso
    (fused (graph core1134) (root 8) 2 0) DegreeOneSmallSpectrum1289.graph fusedMap1134swap=true := by decide +kernel
theorem certified1134swap : Certified (graph core1134) (root 8) 2 0 :=
  of_native_maps core1134 DegreeOneSmallSpectrum1277.graph DegreeOneSmallSpectrum1289.graph
    sourceMap1134swap fusedMap1134swap sourceMap1134swap_checked fusedMap1134swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1134
#print axioms sourceMap1134swap_checked
#print axioms fusedMap1134swap_checked
#print axioms certified1134swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
