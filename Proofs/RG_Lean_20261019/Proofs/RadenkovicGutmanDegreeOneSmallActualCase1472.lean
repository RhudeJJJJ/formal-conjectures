/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1472 : Family 9 := level9.get ⟨206,by decide⟩
def sourceMap1472 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1472 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1472_checked : acceptsGraphIso
    (source (graph core1472) (root 9) 0 1) DegreeOneSmallSpectrum1326.graph sourceMap1472=true := by decide +kernel
theorem fusedMap1472_checked : acceptsGraphIso
    (fused (graph core1472) (root 9) 0 1) DegreeOneSmallSpectrum1331.graph fusedMap1472=true := by decide +kernel
theorem certified1472 : Certified (graph core1472) (root 9) 0 1 :=
  of_native_maps core1472 DegreeOneSmallSpectrum1326.graph DegreeOneSmallSpectrum1331.graph
    sourceMap1472 fusedMap1472 sourceMap1472_checked fusedMap1472_checked
    DegreeOneSmallComparisons.comparison1472
#print axioms sourceMap1472_checked
#print axioms fusedMap1472_checked
#print axioms certified1472
def sourceMap1472swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1472swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1472swap_checked : acceptsGraphIso
    (source (graph core1472) (root 9) 1 0) DegreeOneSmallSpectrum1326.graph sourceMap1472swap=true := by decide +kernel
theorem fusedMap1472swap_checked : acceptsGraphIso
    (fused (graph core1472) (root 9) 1 0) DegreeOneSmallSpectrum1331.graph fusedMap1472swap=true := by decide +kernel
theorem certified1472swap : Certified (graph core1472) (root 9) 1 0 :=
  of_native_maps core1472 DegreeOneSmallSpectrum1326.graph DegreeOneSmallSpectrum1331.graph
    sourceMap1472swap fusedMap1472swap sourceMap1472swap_checked fusedMap1472swap_checked
    DegreeOneSmallComparisons.comparison1472
#print axioms sourceMap1472swap_checked
#print axioms fusedMap1472swap_checked
#print axioms certified1472swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
