/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1064 : Family 8 := level8.get ⟨133,by decide⟩
def sourceMap1064 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1064 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1064_checked : acceptsGraphIso
    (source (graph core1064) (root 8) 0 1) SmallGeFourSpectrum172.graph sourceMap1064=true := by decide +kernel
theorem fusedMap1064_checked : acceptsGraphIso
    (fused (graph core1064) (root 8) 0 1) SmallGeFourSpectrum099.graph fusedMap1064=true := by decide +kernel
theorem certified1064 : Certified (graph core1064) (root 8) 0 1 :=
  of_native_maps core1064 SmallGeFourSpectrum172.graph SmallGeFourSpectrum099.graph
    sourceMap1064 fusedMap1064 sourceMap1064_checked fusedMap1064_checked
    DegreeOneSmallComparisons.comparison1064
#print axioms sourceMap1064_checked
#print axioms fusedMap1064_checked
#print axioms certified1064
def sourceMap1064swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1064swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1064swap_checked : acceptsGraphIso
    (source (graph core1064) (root 8) 1 0) SmallGeFourSpectrum172.graph sourceMap1064swap=true := by decide +kernel
theorem fusedMap1064swap_checked : acceptsGraphIso
    (fused (graph core1064) (root 8) 1 0) SmallGeFourSpectrum099.graph fusedMap1064swap=true := by decide +kernel
theorem certified1064swap : Certified (graph core1064) (root 8) 1 0 :=
  of_native_maps core1064 SmallGeFourSpectrum172.graph SmallGeFourSpectrum099.graph
    sourceMap1064swap fusedMap1064swap sourceMap1064swap_checked fusedMap1064swap_checked
    DegreeOneSmallComparisons.comparison1064
#print axioms sourceMap1064swap_checked
#print axioms fusedMap1064swap_checked
#print axioms certified1064swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
