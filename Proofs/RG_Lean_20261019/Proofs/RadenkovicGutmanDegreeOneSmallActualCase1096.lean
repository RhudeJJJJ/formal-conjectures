/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1096 : Family 8 := level8.get ⟨149,by decide⟩
def sourceMap1096 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1096 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1096_checked : acceptsGraphIso
    (source (graph core1096) (root 8) 0 1) DegreeOneSmallSpectrum812.graph sourceMap1096=true := by decide +kernel
theorem fusedMap1096_checked : acceptsGraphIso
    (fused (graph core1096) (root 8) 0 1) DegreeOneSmallSpectrum535.graph fusedMap1096=true := by decide +kernel
theorem certified1096 : Certified (graph core1096) (root 8) 0 1 :=
  of_native_maps core1096 DegreeOneSmallSpectrum812.graph DegreeOneSmallSpectrum535.graph
    sourceMap1096 fusedMap1096 sourceMap1096_checked fusedMap1096_checked
    DegreeOneSmallComparisons.comparison1096
#print axioms sourceMap1096_checked
#print axioms fusedMap1096_checked
#print axioms certified1096
def sourceMap1096swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1096swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1096swap_checked : acceptsGraphIso
    (source (graph core1096) (root 8) 1 0) DegreeOneSmallSpectrum812.graph sourceMap1096swap=true := by decide +kernel
theorem fusedMap1096swap_checked : acceptsGraphIso
    (fused (graph core1096) (root 8) 1 0) DegreeOneSmallSpectrum535.graph fusedMap1096swap=true := by decide +kernel
theorem certified1096swap : Certified (graph core1096) (root 8) 1 0 :=
  of_native_maps core1096 DegreeOneSmallSpectrum812.graph DegreeOneSmallSpectrum535.graph
    sourceMap1096swap fusedMap1096swap sourceMap1096swap_checked fusedMap1096swap_checked
    DegreeOneSmallComparisons.comparison1096
#print axioms sourceMap1096swap_checked
#print axioms fusedMap1096swap_checked
#print axioms certified1096swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
