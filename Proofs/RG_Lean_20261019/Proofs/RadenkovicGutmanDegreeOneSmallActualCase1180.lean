/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1180 : Family 8 := level8.get ⟨230,by decide⟩
def sourceMap1180 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1180 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1180_checked : acceptsGraphIso
    (source (graph core1180) (root 8) 0 1) SmallGeFourSpectrum165.graph sourceMap1180=true := by decide +kernel
theorem fusedMap1180_checked : acceptsGraphIso
    (fused (graph core1180) (root 8) 0 1) SmallGeFourSpectrum166.graph fusedMap1180=true := by decide +kernel
theorem certified1180 : Certified (graph core1180) (root 8) 0 1 :=
  of_native_maps core1180 SmallGeFourSpectrum165.graph SmallGeFourSpectrum166.graph
    sourceMap1180 fusedMap1180 sourceMap1180_checked fusedMap1180_checked
    DegreeOneSmallComparisons.comparison1180
#print axioms sourceMap1180_checked
#print axioms fusedMap1180_checked
#print axioms certified1180
def sourceMap1180swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1180swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1180swap_checked : acceptsGraphIso
    (source (graph core1180) (root 8) 1 0) SmallGeFourSpectrum165.graph sourceMap1180swap=true := by decide +kernel
theorem fusedMap1180swap_checked : acceptsGraphIso
    (fused (graph core1180) (root 8) 1 0) SmallGeFourSpectrum166.graph fusedMap1180swap=true := by decide +kernel
theorem certified1180swap : Certified (graph core1180) (root 8) 1 0 :=
  of_native_maps core1180 SmallGeFourSpectrum165.graph SmallGeFourSpectrum166.graph
    sourceMap1180swap fusedMap1180swap sourceMap1180swap_checked fusedMap1180swap_checked
    DegreeOneSmallComparisons.comparison1180
#print axioms sourceMap1180swap_checked
#print axioms fusedMap1180swap_checked
#print axioms certified1180swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
