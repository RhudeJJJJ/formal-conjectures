/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1198 : Family 9 := level9.get ⟨1,by decide⟩
def sourceMap1198 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1198 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1198_checked : acceptsGraphIso
    (source (graph core1198) (root 9) 0 1) DegreeOneSmallSpectrum900.graph sourceMap1198=true := by decide +kernel
theorem fusedMap1198_checked : acceptsGraphIso
    (fused (graph core1198) (root 9) 0 1) DegreeOneSmallSpectrum856.graph fusedMap1198=true := by decide +kernel
theorem certified1198 : Certified (graph core1198) (root 9) 0 1 :=
  of_native_maps core1198 DegreeOneSmallSpectrum900.graph DegreeOneSmallSpectrum856.graph
    sourceMap1198 fusedMap1198 sourceMap1198_checked fusedMap1198_checked
    DegreeOneSmallComparisons.comparison1198
#print axioms sourceMap1198_checked
#print axioms fusedMap1198_checked
#print axioms certified1198
def sourceMap1198swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1198swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1198swap_checked : acceptsGraphIso
    (source (graph core1198) (root 9) 1 0) DegreeOneSmallSpectrum900.graph sourceMap1198swap=true := by decide +kernel
theorem fusedMap1198swap_checked : acceptsGraphIso
    (fused (graph core1198) (root 9) 1 0) DegreeOneSmallSpectrum856.graph fusedMap1198swap=true := by decide +kernel
theorem certified1198swap : Certified (graph core1198) (root 9) 1 0 :=
  of_native_maps core1198 DegreeOneSmallSpectrum900.graph DegreeOneSmallSpectrum856.graph
    sourceMap1198swap fusedMap1198swap sourceMap1198swap_checked fusedMap1198swap_checked
    DegreeOneSmallComparisons.comparison1198
#print axioms sourceMap1198swap_checked
#print axioms fusedMap1198swap_checked
#print axioms certified1198swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
