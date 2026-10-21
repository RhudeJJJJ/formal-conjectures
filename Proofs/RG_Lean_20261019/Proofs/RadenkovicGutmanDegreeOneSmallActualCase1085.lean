/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1085 : Family 8 := level8.get ⟨142,by decide⟩
def sourceMap1085 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1085 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1085_checked : acceptsGraphIso
    (source (graph core1085) (root 8) 0 2) DegreeOneSmallSpectrum1357.graph sourceMap1085=true := by decide +kernel
theorem fusedMap1085_checked : acceptsGraphIso
    (fused (graph core1085) (root 8) 0 2) DegreeOneSmallSpectrum1358.graph fusedMap1085=true := by decide +kernel
theorem certified1085 : Certified (graph core1085) (root 8) 0 2 :=
  of_native_maps core1085 DegreeOneSmallSpectrum1357.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1085 fusedMap1085 sourceMap1085_checked fusedMap1085_checked
    DegreeOneSmallComparisons.comparison1085
#print axioms sourceMap1085_checked
#print axioms fusedMap1085_checked
#print axioms certified1085
def sourceMap1085swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1085swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1085swap_checked : acceptsGraphIso
    (source (graph core1085) (root 8) 2 0) DegreeOneSmallSpectrum1357.graph sourceMap1085swap=true := by decide +kernel
theorem fusedMap1085swap_checked : acceptsGraphIso
    (fused (graph core1085) (root 8) 2 0) DegreeOneSmallSpectrum1358.graph fusedMap1085swap=true := by decide +kernel
theorem certified1085swap : Certified (graph core1085) (root 8) 2 0 :=
  of_native_maps core1085 DegreeOneSmallSpectrum1357.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1085swap fusedMap1085swap sourceMap1085swap_checked fusedMap1085swap_checked
    DegreeOneSmallComparisons.comparison1085
#print axioms sourceMap1085swap_checked
#print axioms fusedMap1085swap_checked
#print axioms certified1085swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
