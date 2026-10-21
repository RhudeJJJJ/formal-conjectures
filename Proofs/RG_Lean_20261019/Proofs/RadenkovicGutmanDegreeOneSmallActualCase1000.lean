/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1000 : Family 8 := level8.get ⟨100,by decide⟩
def sourceMap1000 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1000 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1000_checked : acceptsGraphIso
    (source (graph core1000) (root 8) 0 1) DegreeOneSmallSpectrum648.graph sourceMap1000=true := by decide +kernel
theorem fusedMap1000_checked : acceptsGraphIso
    (fused (graph core1000) (root 8) 0 1) DegreeOneSmallSpectrum406.graph fusedMap1000=true := by decide +kernel
theorem certified1000 : Certified (graph core1000) (root 8) 0 1 :=
  of_native_maps core1000 DegreeOneSmallSpectrum648.graph DegreeOneSmallSpectrum406.graph
    sourceMap1000 fusedMap1000 sourceMap1000_checked fusedMap1000_checked
    DegreeOneSmallComparisons.comparison1000
#print axioms sourceMap1000_checked
#print axioms fusedMap1000_checked
#print axioms certified1000
def sourceMap1000swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1000swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1000swap_checked : acceptsGraphIso
    (source (graph core1000) (root 8) 1 0) DegreeOneSmallSpectrum648.graph sourceMap1000swap=true := by decide +kernel
theorem fusedMap1000swap_checked : acceptsGraphIso
    (fused (graph core1000) (root 8) 1 0) DegreeOneSmallSpectrum406.graph fusedMap1000swap=true := by decide +kernel
theorem certified1000swap : Certified (graph core1000) (root 8) 1 0 :=
  of_native_maps core1000 DegreeOneSmallSpectrum648.graph DegreeOneSmallSpectrum406.graph
    sourceMap1000swap fusedMap1000swap sourceMap1000swap_checked fusedMap1000swap_checked
    DegreeOneSmallComparisons.comparison1000
#print axioms sourceMap1000swap_checked
#print axioms fusedMap1000swap_checked
#print axioms certified1000swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
