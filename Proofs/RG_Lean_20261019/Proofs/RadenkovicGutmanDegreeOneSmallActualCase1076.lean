/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1076 : Family 8 := level8.get ⟨137,by decide⟩
def sourceMap1076 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1076 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1076_checked : acceptsGraphIso
    (source (graph core1076) (root 8) 0 1) DegreeOneSmallSpectrum793.graph sourceMap1076=true := by decide +kernel
theorem fusedMap1076_checked : acceptsGraphIso
    (fused (graph core1076) (root 8) 0 1) DegreeOneSmallSpectrum507.graph fusedMap1076=true := by decide +kernel
theorem certified1076 : Certified (graph core1076) (root 8) 0 1 :=
  of_native_maps core1076 DegreeOneSmallSpectrum793.graph DegreeOneSmallSpectrum507.graph
    sourceMap1076 fusedMap1076 sourceMap1076_checked fusedMap1076_checked
    DegreeOneSmallComparisons.comparison1076
#print axioms sourceMap1076_checked
#print axioms fusedMap1076_checked
#print axioms certified1076
def sourceMap1076swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1076swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1076swap_checked : acceptsGraphIso
    (source (graph core1076) (root 8) 1 0) DegreeOneSmallSpectrum793.graph sourceMap1076swap=true := by decide +kernel
theorem fusedMap1076swap_checked : acceptsGraphIso
    (fused (graph core1076) (root 8) 1 0) DegreeOneSmallSpectrum507.graph fusedMap1076swap=true := by decide +kernel
theorem certified1076swap : Certified (graph core1076) (root 8) 1 0 :=
  of_native_maps core1076 DegreeOneSmallSpectrum793.graph DegreeOneSmallSpectrum507.graph
    sourceMap1076swap fusedMap1076swap sourceMap1076swap_checked fusedMap1076swap_checked
    DegreeOneSmallComparisons.comparison1076
#print axioms sourceMap1076swap_checked
#print axioms fusedMap1076swap_checked
#print axioms certified1076swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
