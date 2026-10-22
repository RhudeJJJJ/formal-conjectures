/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1112 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap1112 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1112 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1112_checked : acceptsGraphIso
    (source (graph core1112) (root 8) 0 2) DegreeOneSmallSpectrum1445.graph sourceMap1112=true := by decide +kernel
theorem fusedMap1112_checked : acceptsGraphIso
    (fused (graph core1112) (root 8) 0 2) DegreeOneSmallSpectrum941.graph fusedMap1112=true := by decide +kernel
theorem certified1112 : Certified (graph core1112) (root 8) 0 2 :=
  of_native_maps core1112 DegreeOneSmallSpectrum1445.graph DegreeOneSmallSpectrum941.graph
    sourceMap1112 fusedMap1112 sourceMap1112_checked fusedMap1112_checked
    DegreeTwoThreeFiniteComparisons.comparison1112
#print axioms sourceMap1112_checked
#print axioms fusedMap1112_checked
#print axioms certified1112
def sourceMap1112swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1112swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1112swap_checked : acceptsGraphIso
    (source (graph core1112) (root 8) 2 0) DegreeOneSmallSpectrum1445.graph sourceMap1112swap=true := by decide +kernel
theorem fusedMap1112swap_checked : acceptsGraphIso
    (fused (graph core1112) (root 8) 2 0) DegreeOneSmallSpectrum941.graph fusedMap1112swap=true := by decide +kernel
theorem certified1112swap : Certified (graph core1112) (root 8) 2 0 :=
  of_native_maps core1112 DegreeOneSmallSpectrum1445.graph DegreeOneSmallSpectrum941.graph
    sourceMap1112swap fusedMap1112swap sourceMap1112swap_checked fusedMap1112swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1112
#print axioms sourceMap1112swap_checked
#print axioms fusedMap1112swap_checked
#print axioms certified1112swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
