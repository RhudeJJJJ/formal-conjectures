/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1536 : Family 9 := level9.get ⟨263,by decide⟩
def sourceMap1536 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1536 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1536_checked : acceptsGraphIso
    (source (graph core1536) (root 9) 0 1) DegreeOneSmallSpectrum1421.graph sourceMap1536=true := by decide +kernel
theorem fusedMap1536_checked : acceptsGraphIso
    (fused (graph core1536) (root 9) 0 1) DegreeOneSmallSpectrum1491.graph fusedMap1536=true := by decide +kernel
theorem certified1536 : Certified (graph core1536) (root 9) 0 1 :=
  of_native_maps core1536 DegreeOneSmallSpectrum1421.graph DegreeOneSmallSpectrum1491.graph
    sourceMap1536 fusedMap1536 sourceMap1536_checked fusedMap1536_checked
    DegreeOneSmallComparisons.comparison1536
#print axioms sourceMap1536_checked
#print axioms fusedMap1536_checked
#print axioms certified1536
def sourceMap1536swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1536swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1536swap_checked : acceptsGraphIso
    (source (graph core1536) (root 9) 1 0) DegreeOneSmallSpectrum1421.graph sourceMap1536swap=true := by decide +kernel
theorem fusedMap1536swap_checked : acceptsGraphIso
    (fused (graph core1536) (root 9) 1 0) DegreeOneSmallSpectrum1491.graph fusedMap1536swap=true := by decide +kernel
theorem certified1536swap : Certified (graph core1536) (root 9) 1 0 :=
  of_native_maps core1536 DegreeOneSmallSpectrum1421.graph DegreeOneSmallSpectrum1491.graph
    sourceMap1536swap fusedMap1536swap sourceMap1536swap_checked fusedMap1536swap_checked
    DegreeOneSmallComparisons.comparison1536
#print axioms sourceMap1536swap_checked
#print axioms fusedMap1536swap_checked
#print axioms certified1536swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
