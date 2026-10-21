/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1214 : Family 9 := level9.get ⟨10,by decide⟩
def sourceMap1214 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1214 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1214_checked : acceptsGraphIso
    (source (graph core1214) (root 9) 0 1) DegreeOneSmallSpectrum876.graph sourceMap1214=true := by decide +kernel
theorem fusedMap1214_checked : acceptsGraphIso
    (fused (graph core1214) (root 9) 0 1) DegreeOneSmallSpectrum879.graph fusedMap1214=true := by decide +kernel
theorem certified1214 : Certified (graph core1214) (root 9) 0 1 :=
  of_native_maps core1214 DegreeOneSmallSpectrum876.graph DegreeOneSmallSpectrum879.graph
    sourceMap1214 fusedMap1214 sourceMap1214_checked fusedMap1214_checked
    DegreeOneSmallComparisons.comparison1214
#print axioms sourceMap1214_checked
#print axioms fusedMap1214_checked
#print axioms certified1214
def sourceMap1214swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1214swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1214swap_checked : acceptsGraphIso
    (source (graph core1214) (root 9) 1 0) DegreeOneSmallSpectrum876.graph sourceMap1214swap=true := by decide +kernel
theorem fusedMap1214swap_checked : acceptsGraphIso
    (fused (graph core1214) (root 9) 1 0) DegreeOneSmallSpectrum879.graph fusedMap1214swap=true := by decide +kernel
theorem certified1214swap : Certified (graph core1214) (root 9) 1 0 :=
  of_native_maps core1214 DegreeOneSmallSpectrum876.graph DegreeOneSmallSpectrum879.graph
    sourceMap1214swap fusedMap1214swap sourceMap1214swap_checked fusedMap1214swap_checked
    DegreeOneSmallComparisons.comparison1214
#print axioms sourceMap1214swap_checked
#print axioms fusedMap1214swap_checked
#print axioms certified1214swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
