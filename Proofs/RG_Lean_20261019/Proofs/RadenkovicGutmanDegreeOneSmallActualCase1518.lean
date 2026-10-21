/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1518 : Family 9 := level9.get ⟨251,by decide⟩
def sourceMap1518 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1518 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1518_checked : acceptsGraphIso
    (source (graph core1518) (root 9) 0 1) DegreeOneSmallSpectrum1438.graph sourceMap1518=true := by decide +kernel
theorem fusedMap1518_checked : acceptsGraphIso
    (fused (graph core1518) (root 9) 0 1) DegreeOneSmallSpectrum1459.graph fusedMap1518=true := by decide +kernel
theorem certified1518 : Certified (graph core1518) (root 9) 0 1 :=
  of_native_maps core1518 DegreeOneSmallSpectrum1438.graph DegreeOneSmallSpectrum1459.graph
    sourceMap1518 fusedMap1518 sourceMap1518_checked fusedMap1518_checked
    DegreeOneSmallComparisons.comparison1518
#print axioms sourceMap1518_checked
#print axioms fusedMap1518_checked
#print axioms certified1518
def sourceMap1518swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1518swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1518swap_checked : acceptsGraphIso
    (source (graph core1518) (root 9) 1 0) DegreeOneSmallSpectrum1438.graph sourceMap1518swap=true := by decide +kernel
theorem fusedMap1518swap_checked : acceptsGraphIso
    (fused (graph core1518) (root 9) 1 0) DegreeOneSmallSpectrum1459.graph fusedMap1518swap=true := by decide +kernel
theorem certified1518swap : Certified (graph core1518) (root 9) 1 0 :=
  of_native_maps core1518 DegreeOneSmallSpectrum1438.graph DegreeOneSmallSpectrum1459.graph
    sourceMap1518swap fusedMap1518swap sourceMap1518swap_checked fusedMap1518swap_checked
    DegreeOneSmallComparisons.comparison1518
#print axioms sourceMap1518swap_checked
#print axioms fusedMap1518swap_checked
#print axioms certified1518swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
