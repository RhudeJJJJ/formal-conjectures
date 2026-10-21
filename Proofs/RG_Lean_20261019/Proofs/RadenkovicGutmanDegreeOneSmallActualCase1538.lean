/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1538 : Family 9 := level9.get ⟨267,by decide⟩
def sourceMap1538 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1538 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1538_checked : acceptsGraphIso
    (source (graph core1538) (root 9) 0 1) DegreeOneSmallSpectrum1447.graph sourceMap1538=true := by decide +kernel
theorem fusedMap1538_checked : acceptsGraphIso
    (fused (graph core1538) (root 9) 0 1) DegreeOneSmallSpectrum1494.graph fusedMap1538=true := by decide +kernel
theorem certified1538 : Certified (graph core1538) (root 9) 0 1 :=
  of_native_maps core1538 DegreeOneSmallSpectrum1447.graph DegreeOneSmallSpectrum1494.graph
    sourceMap1538 fusedMap1538 sourceMap1538_checked fusedMap1538_checked
    DegreeOneSmallComparisons.comparison1538
#print axioms sourceMap1538_checked
#print axioms fusedMap1538_checked
#print axioms certified1538
def sourceMap1538swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1538swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1538swap_checked : acceptsGraphIso
    (source (graph core1538) (root 9) 1 0) DegreeOneSmallSpectrum1447.graph sourceMap1538swap=true := by decide +kernel
theorem fusedMap1538swap_checked : acceptsGraphIso
    (fused (graph core1538) (root 9) 1 0) DegreeOneSmallSpectrum1494.graph fusedMap1538swap=true := by decide +kernel
theorem certified1538swap : Certified (graph core1538) (root 9) 1 0 :=
  of_native_maps core1538 DegreeOneSmallSpectrum1447.graph DegreeOneSmallSpectrum1494.graph
    sourceMap1538swap fusedMap1538swap sourceMap1538swap_checked fusedMap1538swap_checked
    DegreeOneSmallComparisons.comparison1538
#print axioms sourceMap1538swap_checked
#print axioms fusedMap1538swap_checked
#print axioms certified1538swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
