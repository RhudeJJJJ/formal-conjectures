/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1108 : Family 8 := level8.get ⟨153,by decide⟩
def sourceMap1108 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1108 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1108_checked : acceptsGraphIso
    (source (graph core1108) (root 8) 0 1) DegreeOneSmallSpectrum815.graph sourceMap1108=true := by decide +kernel
theorem fusedMap1108_checked : acceptsGraphIso
    (fused (graph core1108) (root 8) 0 1) SmallGeFourSpectrum105.graph fusedMap1108=true := by decide +kernel
theorem certified1108 : Certified (graph core1108) (root 8) 0 1 :=
  of_native_maps core1108 DegreeOneSmallSpectrum815.graph SmallGeFourSpectrum105.graph
    sourceMap1108 fusedMap1108 sourceMap1108_checked fusedMap1108_checked
    DegreeOneSmallComparisons.comparison1108
#print axioms sourceMap1108_checked
#print axioms fusedMap1108_checked
#print axioms certified1108
def sourceMap1108swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1108swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1108swap_checked : acceptsGraphIso
    (source (graph core1108) (root 8) 1 0) DegreeOneSmallSpectrum815.graph sourceMap1108swap=true := by decide +kernel
theorem fusedMap1108swap_checked : acceptsGraphIso
    (fused (graph core1108) (root 8) 1 0) SmallGeFourSpectrum105.graph fusedMap1108swap=true := by decide +kernel
theorem certified1108swap : Certified (graph core1108) (root 8) 1 0 :=
  of_native_maps core1108 DegreeOneSmallSpectrum815.graph SmallGeFourSpectrum105.graph
    sourceMap1108swap fusedMap1108swap sourceMap1108swap_checked fusedMap1108swap_checked
    DegreeOneSmallComparisons.comparison1108
#print axioms sourceMap1108swap_checked
#print axioms fusedMap1108swap_checked
#print axioms certified1108swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
