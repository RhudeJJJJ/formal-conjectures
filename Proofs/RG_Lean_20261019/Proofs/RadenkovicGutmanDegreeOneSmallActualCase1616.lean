/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1616 : Family 9 := level9.get ⟨358,by decide⟩
def sourceMap1616 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1616 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1616_checked : acceptsGraphIso
    (source (graph core1616) (root 9) 0 1) DegreeOneSmallSpectrum1742.graph sourceMap1616=true := by decide +kernel
theorem fusedMap1616_checked : acceptsGraphIso
    (fused (graph core1616) (root 9) 0 1) DegreeOneSmallSpectrum1090.graph fusedMap1616=true := by decide +kernel
theorem certified1616 : Certified (graph core1616) (root 9) 0 1 :=
  of_native_maps core1616 DegreeOneSmallSpectrum1742.graph DegreeOneSmallSpectrum1090.graph
    sourceMap1616 fusedMap1616 sourceMap1616_checked fusedMap1616_checked
    DegreeOneSmallComparisons.comparison1616
#print axioms sourceMap1616_checked
#print axioms fusedMap1616_checked
#print axioms certified1616
def sourceMap1616swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1616swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1616swap_checked : acceptsGraphIso
    (source (graph core1616) (root 9) 1 0) DegreeOneSmallSpectrum1742.graph sourceMap1616swap=true := by decide +kernel
theorem fusedMap1616swap_checked : acceptsGraphIso
    (fused (graph core1616) (root 9) 1 0) DegreeOneSmallSpectrum1090.graph fusedMap1616swap=true := by decide +kernel
theorem certified1616swap : Certified (graph core1616) (root 9) 1 0 :=
  of_native_maps core1616 DegreeOneSmallSpectrum1742.graph DegreeOneSmallSpectrum1090.graph
    sourceMap1616swap fusedMap1616swap sourceMap1616swap_checked fusedMap1616swap_checked
    DegreeOneSmallComparisons.comparison1616
#print axioms sourceMap1616swap_checked
#print axioms fusedMap1616swap_checked
#print axioms certified1616swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
