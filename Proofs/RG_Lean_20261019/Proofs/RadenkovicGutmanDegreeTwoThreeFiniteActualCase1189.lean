/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1189 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap1189 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 0 2 v)
def fusedMap1189 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1189_checked : acceptsGraphIso
    (source (graph core1189) (root 8) 0 2) DegreeOneSmallSpectrum1533.graph sourceMap1189=true := by decide +kernel
theorem fusedMap1189_checked : acceptsGraphIso
    (fused (graph core1189) (root 8) 0 2) DegreeOneSmallSpectrum1536.graph fusedMap1189=true := by decide +kernel
theorem certified1189 : Certified (graph core1189) (root 8) 0 2 :=
  of_native_maps core1189 DegreeOneSmallSpectrum1533.graph DegreeOneSmallSpectrum1536.graph
    sourceMap1189 fusedMap1189 sourceMap1189_checked fusedMap1189_checked
    DegreeTwoThreeFiniteComparisons.comparison1189
#print axioms sourceMap1189_checked
#print axioms fusedMap1189_checked
#print axioms certified1189
def sourceMap1189swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,9] (sourceLabel 8 2 0 v)
def fusedMap1189swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1189swap_checked : acceptsGraphIso
    (source (graph core1189) (root 8) 2 0) DegreeOneSmallSpectrum1533.graph sourceMap1189swap=true := by decide +kernel
theorem fusedMap1189swap_checked : acceptsGraphIso
    (fused (graph core1189) (root 8) 2 0) DegreeOneSmallSpectrum1536.graph fusedMap1189swap=true := by decide +kernel
theorem certified1189swap : Certified (graph core1189) (root 8) 2 0 :=
  of_native_maps core1189 DegreeOneSmallSpectrum1533.graph DegreeOneSmallSpectrum1536.graph
    sourceMap1189swap fusedMap1189swap sourceMap1189swap_checked fusedMap1189swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1189
#print axioms sourceMap1189swap_checked
#print axioms fusedMap1189swap_checked
#print axioms certified1189swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
