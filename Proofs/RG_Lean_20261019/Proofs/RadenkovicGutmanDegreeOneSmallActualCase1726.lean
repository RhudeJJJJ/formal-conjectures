/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1726 : Family 9 := level9.get ⟨543,by decide⟩
def sourceMap1726 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1726 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1726_checked : acceptsGraphIso
    (source (graph core1726) (root 9) 0 1) DegreeOneSmallSpectrum1525.graph sourceMap1726=true := by decide +kernel
theorem fusedMap1726_checked : acceptsGraphIso
    (fused (graph core1726) (root 9) 0 1) DegreeOneSmallSpectrum1526.graph fusedMap1726=true := by decide +kernel
theorem certified1726 : Certified (graph core1726) (root 9) 0 1 :=
  of_native_maps core1726 DegreeOneSmallSpectrum1525.graph DegreeOneSmallSpectrum1526.graph
    sourceMap1726 fusedMap1726 sourceMap1726_checked fusedMap1726_checked
    DegreeOneSmallComparisons.comparison1726
#print axioms sourceMap1726_checked
#print axioms fusedMap1726_checked
#print axioms certified1726
def sourceMap1726swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1726swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1726swap_checked : acceptsGraphIso
    (source (graph core1726) (root 9) 1 0) DegreeOneSmallSpectrum1525.graph sourceMap1726swap=true := by decide +kernel
theorem fusedMap1726swap_checked : acceptsGraphIso
    (fused (graph core1726) (root 9) 1 0) DegreeOneSmallSpectrum1526.graph fusedMap1726swap=true := by decide +kernel
theorem certified1726swap : Certified (graph core1726) (root 9) 1 0 :=
  of_native_maps core1726 DegreeOneSmallSpectrum1525.graph DegreeOneSmallSpectrum1526.graph
    sourceMap1726swap fusedMap1726swap sourceMap1726swap_checked fusedMap1726swap_checked
    DegreeOneSmallComparisons.comparison1726
#print axioms sourceMap1726swap_checked
#print axioms fusedMap1726swap_checked
#print axioms certified1726swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
