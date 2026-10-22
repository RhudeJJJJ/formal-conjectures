/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1027 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap1027 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![4,0,1,2,3,7,8,5,6] (sourceLabel 5 0 1 v)
def fusedMap1027 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (fusedLabel 5 0 1 v)
theorem sourceMap1027_checked : acceptsGraphIso
    (source (graph core1027) (root 5) 0 1) DegreeOneSmallSpectrum050.graph sourceMap1027=true := by decide +kernel
theorem fusedMap1027_checked : acceptsGraphIso
    (fused (graph core1027) (root 5) 0 1) DegreeOneSmallSpectrum052.graph fusedMap1027=true := by decide +kernel
theorem certified1027 : Certified (graph core1027) (root 5) 0 1 :=
  of_native_maps core1027 DegreeOneSmallSpectrum050.graph DegreeOneSmallSpectrum052.graph
    sourceMap1027 fusedMap1027 sourceMap1027_checked fusedMap1027_checked
    DegreeTwoThreeFiniteComparisons.comparison1027
#print axioms sourceMap1027_checked
#print axioms fusedMap1027_checked
#print axioms certified1027
def sourceMap1027swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![4,0,1,2,3,7,5,6,8] (sourceLabel 5 1 0 v)
def fusedMap1027swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (fusedLabel 5 1 0 v)
theorem sourceMap1027swap_checked : acceptsGraphIso
    (source (graph core1027) (root 5) 1 0) DegreeOneSmallSpectrum050.graph sourceMap1027swap=true := by decide +kernel
theorem fusedMap1027swap_checked : acceptsGraphIso
    (fused (graph core1027) (root 5) 1 0) DegreeOneSmallSpectrum052.graph fusedMap1027swap=true := by decide +kernel
theorem certified1027swap : Certified (graph core1027) (root 5) 1 0 :=
  of_native_maps core1027 DegreeOneSmallSpectrum050.graph DegreeOneSmallSpectrum052.graph
    sourceMap1027swap fusedMap1027swap sourceMap1027swap_checked fusedMap1027swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1027
#print axioms sourceMap1027swap_checked
#print axioms fusedMap1027swap_checked
#print axioms certified1027swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
