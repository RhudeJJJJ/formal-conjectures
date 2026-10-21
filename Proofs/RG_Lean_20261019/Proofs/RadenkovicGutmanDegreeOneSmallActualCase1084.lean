/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1084 : Family 8 := level8.get ⟨142,by decide⟩
def sourceMap1084 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap1084 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1084_checked : acceptsGraphIso
    (source (graph core1084) (root 8) 0 1) SmallGeFourSpectrum186.graph sourceMap1084=true := by decide +kernel
theorem fusedMap1084_checked : acceptsGraphIso
    (fused (graph core1084) (root 8) 0 1) SmallGeFourSpectrum101.graph fusedMap1084=true := by decide +kernel
theorem certified1084 : Certified (graph core1084) (root 8) 0 1 :=
  of_native_maps core1084 SmallGeFourSpectrum186.graph SmallGeFourSpectrum101.graph
    sourceMap1084 fusedMap1084 sourceMap1084_checked fusedMap1084_checked
    DegreeOneSmallComparisons.comparison1084
#print axioms sourceMap1084_checked
#print axioms fusedMap1084_checked
#print axioms certified1084
def sourceMap1084swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap1084swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1084swap_checked : acceptsGraphIso
    (source (graph core1084) (root 8) 1 0) SmallGeFourSpectrum186.graph sourceMap1084swap=true := by decide +kernel
theorem fusedMap1084swap_checked : acceptsGraphIso
    (fused (graph core1084) (root 8) 1 0) SmallGeFourSpectrum101.graph fusedMap1084swap=true := by decide +kernel
theorem certified1084swap : Certified (graph core1084) (root 8) 1 0 :=
  of_native_maps core1084 SmallGeFourSpectrum186.graph SmallGeFourSpectrum101.graph
    sourceMap1084swap fusedMap1084swap sourceMap1084swap_checked fusedMap1084swap_checked
    DegreeOneSmallComparisons.comparison1084
#print axioms sourceMap1084swap_checked
#print axioms fusedMap1084swap_checked
#print axioms certified1084swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
