/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1005 : Family 8 := level8.get ⟨101,by decide⟩
def sourceMap1005 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1005 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1005_checked : acceptsGraphIso
    (source (graph core1005) (root 8) 0 2) DegreeOneSmallSpectrum1026.graph sourceMap1005=true := by decide +kernel
theorem fusedMap1005_checked : acceptsGraphIso
    (fused (graph core1005) (root 8) 0 2) DegreeOneSmallSpectrum1027.graph fusedMap1005=true := by decide +kernel
theorem certified1005 : Certified (graph core1005) (root 8) 0 2 :=
  of_native_maps core1005 DegreeOneSmallSpectrum1026.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1005 fusedMap1005 sourceMap1005_checked fusedMap1005_checked
    DegreeOneSmallComparisons.comparison1005
#print axioms sourceMap1005_checked
#print axioms fusedMap1005_checked
#print axioms certified1005
def sourceMap1005swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1005swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1005swap_checked : acceptsGraphIso
    (source (graph core1005) (root 8) 2 0) DegreeOneSmallSpectrum1026.graph sourceMap1005swap=true := by decide +kernel
theorem fusedMap1005swap_checked : acceptsGraphIso
    (fused (graph core1005) (root 8) 2 0) DegreeOneSmallSpectrum1027.graph fusedMap1005swap=true := by decide +kernel
theorem certified1005swap : Certified (graph core1005) (root 8) 2 0 :=
  of_native_maps core1005 DegreeOneSmallSpectrum1026.graph DegreeOneSmallSpectrum1027.graph
    sourceMap1005swap fusedMap1005swap sourceMap1005swap_checked fusedMap1005swap_checked
    DegreeOneSmallComparisons.comparison1005
#print axioms sourceMap1005swap_checked
#print axioms fusedMap1005swap_checked
#print axioms certified1005swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
