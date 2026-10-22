/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1035 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap1035 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 0 2 v)
def fusedMap1035 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap1035_checked : acceptsGraphIso
    (source (graph core1035) (root 4) 0 2) DegreeOneSmallSpectrum044.graph sourceMap1035=true := by decide +kernel
theorem fusedMap1035_checked : acceptsGraphIso
    (fused (graph core1035) (root 4) 0 2) DegreeOneSmallSpectrum047.graph fusedMap1035=true := by decide +kernel
theorem certified1035 : Certified (graph core1035) (root 4) 0 2 :=
  of_native_maps core1035 DegreeOneSmallSpectrum044.graph DegreeOneSmallSpectrum047.graph
    sourceMap1035 fusedMap1035 sourceMap1035_checked fusedMap1035_checked
    DegreeTwoThreeFiniteComparisons.comparison1035
#print axioms sourceMap1035_checked
#print axioms fusedMap1035_checked
#print axioms certified1035
def sourceMap1035swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,6,7,8,5] (sourceLabel 4 2 0 v)
def fusedMap1035swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap1035swap_checked : acceptsGraphIso
    (source (graph core1035) (root 4) 2 0) DegreeOneSmallSpectrum044.graph sourceMap1035swap=true := by decide +kernel
theorem fusedMap1035swap_checked : acceptsGraphIso
    (fused (graph core1035) (root 4) 2 0) DegreeOneSmallSpectrum047.graph fusedMap1035swap=true := by decide +kernel
theorem certified1035swap : Certified (graph core1035) (root 4) 2 0 :=
  of_native_maps core1035 DegreeOneSmallSpectrum044.graph DegreeOneSmallSpectrum047.graph
    sourceMap1035swap fusedMap1035swap sourceMap1035swap_checked fusedMap1035swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1035
#print axioms sourceMap1035swap_checked
#print axioms fusedMap1035swap_checked
#print axioms certified1035swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
