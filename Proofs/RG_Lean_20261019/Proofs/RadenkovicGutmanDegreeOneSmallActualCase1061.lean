/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1061 : Family 8 := level8.get ⟨132,by decide⟩
def sourceMap1061 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1061 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1061_checked : acceptsGraphIso
    (source (graph core1061) (root 8) 0 2) DegreeOneSmallSpectrum1295.graph sourceMap1061=true := by decide +kernel
theorem fusedMap1061_checked : acceptsGraphIso
    (fused (graph core1061) (root 8) 0 2) DegreeOneSmallSpectrum1296.graph fusedMap1061=true := by decide +kernel
theorem certified1061 : Certified (graph core1061) (root 8) 0 2 :=
  of_native_maps core1061 DegreeOneSmallSpectrum1295.graph DegreeOneSmallSpectrum1296.graph
    sourceMap1061 fusedMap1061 sourceMap1061_checked fusedMap1061_checked
    DegreeOneSmallComparisons.comparison1061
#print axioms sourceMap1061_checked
#print axioms fusedMap1061_checked
#print axioms certified1061
def sourceMap1061swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1061swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1061swap_checked : acceptsGraphIso
    (source (graph core1061) (root 8) 2 0) DegreeOneSmallSpectrum1295.graph sourceMap1061swap=true := by decide +kernel
theorem fusedMap1061swap_checked : acceptsGraphIso
    (fused (graph core1061) (root 8) 2 0) DegreeOneSmallSpectrum1296.graph fusedMap1061swap=true := by decide +kernel
theorem certified1061swap : Certified (graph core1061) (root 8) 2 0 :=
  of_native_maps core1061 DegreeOneSmallSpectrum1295.graph DegreeOneSmallSpectrum1296.graph
    sourceMap1061swap fusedMap1061swap sourceMap1061swap_checked fusedMap1061swap_checked
    DegreeOneSmallComparisons.comparison1061
#print axioms sourceMap1061swap_checked
#print axioms fusedMap1061swap_checked
#print axioms certified1061swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
