/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1528 : Family 9 := level9.get ⟨258,by decide⟩
def sourceMap1528 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1528 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1528_checked : acceptsGraphIso
    (source (graph core1528) (root 9) 0 1) DegreeOneSmallSpectrum1443.graph sourceMap1528=true := by decide +kernel
theorem fusedMap1528_checked : acceptsGraphIso
    (fused (graph core1528) (root 9) 0 1) DegreeOneSmallSpectrum1478.graph fusedMap1528=true := by decide +kernel
theorem certified1528 : Certified (graph core1528) (root 9) 0 1 :=
  of_native_maps core1528 DegreeOneSmallSpectrum1443.graph DegreeOneSmallSpectrum1478.graph
    sourceMap1528 fusedMap1528 sourceMap1528_checked fusedMap1528_checked
    DegreeOneSmallComparisons.comparison1528
#print axioms sourceMap1528_checked
#print axioms fusedMap1528_checked
#print axioms certified1528
def sourceMap1528swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1528swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1528swap_checked : acceptsGraphIso
    (source (graph core1528) (root 9) 1 0) DegreeOneSmallSpectrum1443.graph sourceMap1528swap=true := by decide +kernel
theorem fusedMap1528swap_checked : acceptsGraphIso
    (fused (graph core1528) (root 9) 1 0) DegreeOneSmallSpectrum1478.graph fusedMap1528swap=true := by decide +kernel
theorem certified1528swap : Certified (graph core1528) (root 9) 1 0 :=
  of_native_maps core1528 DegreeOneSmallSpectrum1443.graph DegreeOneSmallSpectrum1478.graph
    sourceMap1528swap fusedMap1528swap sourceMap1528swap_checked fusedMap1528swap_checked
    DegreeOneSmallComparisons.comparison1528
#print axioms sourceMap1528swap_checked
#print axioms fusedMap1528swap_checked
#print axioms certified1528swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
