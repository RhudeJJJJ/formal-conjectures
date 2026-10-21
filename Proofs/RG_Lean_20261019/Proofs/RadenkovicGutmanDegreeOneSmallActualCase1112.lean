/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1112 : Family 8 := level8.get ⟨161,by decide⟩
def sourceMap1112 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1112 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1112_checked : acceptsGraphIso
    (source (graph core1112) (root 8) 0 1) DegreeOneSmallSpectrum816.graph sourceMap1112=true := by decide +kernel
theorem fusedMap1112_checked : acceptsGraphIso
    (fused (graph core1112) (root 8) 0 1) DegreeOneSmallSpectrum561.graph fusedMap1112=true := by decide +kernel
theorem certified1112 : Certified (graph core1112) (root 8) 0 1 :=
  of_native_maps core1112 DegreeOneSmallSpectrum816.graph DegreeOneSmallSpectrum561.graph
    sourceMap1112 fusedMap1112 sourceMap1112_checked fusedMap1112_checked
    DegreeOneSmallComparisons.comparison1112
#print axioms sourceMap1112_checked
#print axioms fusedMap1112_checked
#print axioms certified1112
def sourceMap1112swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1112swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1112swap_checked : acceptsGraphIso
    (source (graph core1112) (root 8) 1 0) DegreeOneSmallSpectrum816.graph sourceMap1112swap=true := by decide +kernel
theorem fusedMap1112swap_checked : acceptsGraphIso
    (fused (graph core1112) (root 8) 1 0) DegreeOneSmallSpectrum561.graph fusedMap1112swap=true := by decide +kernel
theorem certified1112swap : Certified (graph core1112) (root 8) 1 0 :=
  of_native_maps core1112 DegreeOneSmallSpectrum816.graph DegreeOneSmallSpectrum561.graph
    sourceMap1112swap fusedMap1112swap sourceMap1112swap_checked fusedMap1112swap_checked
    DegreeOneSmallComparisons.comparison1112
#print axioms sourceMap1112swap_checked
#print axioms fusedMap1112swap_checked
#print axioms certified1112swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
