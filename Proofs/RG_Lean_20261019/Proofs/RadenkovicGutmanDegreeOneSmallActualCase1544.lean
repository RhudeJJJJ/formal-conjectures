/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1544 : Family 9 := level9.get ⟨271,by decide⟩
def sourceMap1544 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1544 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1544_checked : acceptsGraphIso
    (source (graph core1544) (root 9) 0 1) DegreeOneSmallSpectrum1422.graph sourceMap1544=true := by decide +kernel
theorem fusedMap1544_checked : acceptsGraphIso
    (fused (graph core1544) (root 9) 0 1) DegreeOneSmallSpectrum1501.graph fusedMap1544=true := by decide +kernel
theorem certified1544 : Certified (graph core1544) (root 9) 0 1 :=
  of_native_maps core1544 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1501.graph
    sourceMap1544 fusedMap1544 sourceMap1544_checked fusedMap1544_checked
    DegreeOneSmallComparisons.comparison1544
#print axioms sourceMap1544_checked
#print axioms fusedMap1544_checked
#print axioms certified1544
def sourceMap1544swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1544swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1544swap_checked : acceptsGraphIso
    (source (graph core1544) (root 9) 1 0) DegreeOneSmallSpectrum1422.graph sourceMap1544swap=true := by decide +kernel
theorem fusedMap1544swap_checked : acceptsGraphIso
    (fused (graph core1544) (root 9) 1 0) DegreeOneSmallSpectrum1501.graph fusedMap1544swap=true := by decide +kernel
theorem certified1544swap : Certified (graph core1544) (root 9) 1 0 :=
  of_native_maps core1544 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1501.graph
    sourceMap1544swap fusedMap1544swap sourceMap1544swap_checked fusedMap1544swap_checked
    DegreeOneSmallComparisons.comparison1544
#print axioms sourceMap1544swap_checked
#print axioms fusedMap1544swap_checked
#print axioms certified1544swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
