/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1004 : Family 8 := level8.get ⟨101,by decide⟩
def sourceMap1004 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap1004 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1004_checked : acceptsGraphIso
    (source (graph core1004) (root 8) 0 1) DegreeOneSmallSpectrum655.graph sourceMap1004=true := by decide +kernel
theorem fusedMap1004_checked : acceptsGraphIso
    (fused (graph core1004) (root 8) 0 1) DegreeOneSmallSpectrum407.graph fusedMap1004=true := by decide +kernel
theorem certified1004 : Certified (graph core1004) (root 8) 0 1 :=
  of_native_maps core1004 DegreeOneSmallSpectrum655.graph DegreeOneSmallSpectrum407.graph
    sourceMap1004 fusedMap1004 sourceMap1004_checked fusedMap1004_checked
    DegreeOneSmallComparisons.comparison1004
#print axioms sourceMap1004_checked
#print axioms fusedMap1004_checked
#print axioms certified1004
def sourceMap1004swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap1004swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1004swap_checked : acceptsGraphIso
    (source (graph core1004) (root 8) 1 0) DegreeOneSmallSpectrum655.graph sourceMap1004swap=true := by decide +kernel
theorem fusedMap1004swap_checked : acceptsGraphIso
    (fused (graph core1004) (root 8) 1 0) DegreeOneSmallSpectrum407.graph fusedMap1004swap=true := by decide +kernel
theorem certified1004swap : Certified (graph core1004) (root 8) 1 0 :=
  of_native_maps core1004 DegreeOneSmallSpectrum655.graph DegreeOneSmallSpectrum407.graph
    sourceMap1004swap fusedMap1004swap sourceMap1004swap_checked fusedMap1004swap_checked
    DegreeOneSmallComparisons.comparison1004
#print axioms sourceMap1004swap_checked
#print axioms fusedMap1004swap_checked
#print axioms certified1004swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
