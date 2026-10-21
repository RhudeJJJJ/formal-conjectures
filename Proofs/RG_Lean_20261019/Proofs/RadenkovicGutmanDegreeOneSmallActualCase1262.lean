/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1262 : Family 9 := level9.get ⟨39,by decide⟩
def sourceMap1262 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1262 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1262_checked : acceptsGraphIso
    (source (graph core1262) (root 9) 0 1) DegreeOneSmallSpectrum924.graph sourceMap1262=true := by decide +kernel
theorem fusedMap1262_checked : acceptsGraphIso
    (fused (graph core1262) (root 9) 0 1) DegreeOneSmallSpectrum974.graph fusedMap1262=true := by decide +kernel
theorem certified1262 : Certified (graph core1262) (root 9) 0 1 :=
  of_native_maps core1262 DegreeOneSmallSpectrum924.graph DegreeOneSmallSpectrum974.graph
    sourceMap1262 fusedMap1262 sourceMap1262_checked fusedMap1262_checked
    DegreeOneSmallComparisons.comparison1262
#print axioms sourceMap1262_checked
#print axioms fusedMap1262_checked
#print axioms certified1262
def sourceMap1262swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1262swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1262swap_checked : acceptsGraphIso
    (source (graph core1262) (root 9) 1 0) DegreeOneSmallSpectrum924.graph sourceMap1262swap=true := by decide +kernel
theorem fusedMap1262swap_checked : acceptsGraphIso
    (fused (graph core1262) (root 9) 1 0) DegreeOneSmallSpectrum974.graph fusedMap1262swap=true := by decide +kernel
theorem certified1262swap : Certified (graph core1262) (root 9) 1 0 :=
  of_native_maps core1262 DegreeOneSmallSpectrum924.graph DegreeOneSmallSpectrum974.graph
    sourceMap1262swap fusedMap1262swap sourceMap1262swap_checked fusedMap1262swap_checked
    DegreeOneSmallComparisons.comparison1262
#print axioms sourceMap1262swap_checked
#print axioms fusedMap1262swap_checked
#print axioms certified1262swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
