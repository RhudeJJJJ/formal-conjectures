/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1172 : Family 8 := level8.get ⟨210,by decide⟩
def sourceMap1172 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1172 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1172_checked : acceptsGraphIso
    (source (graph core1172) (root 8) 0 1) SmallGeFourSpectrum143.graph sourceMap1172=true := by decide +kernel
theorem fusedMap1172_checked : acceptsGraphIso
    (fused (graph core1172) (root 8) 0 1) SmallGeFourSpectrum144.graph fusedMap1172=true := by decide +kernel
theorem certified1172 : Certified (graph core1172) (root 8) 0 1 :=
  of_native_maps core1172 SmallGeFourSpectrum143.graph SmallGeFourSpectrum144.graph
    sourceMap1172 fusedMap1172 sourceMap1172_checked fusedMap1172_checked
    DegreeOneSmallComparisons.comparison1172
#print axioms sourceMap1172_checked
#print axioms fusedMap1172_checked
#print axioms certified1172
def sourceMap1172swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1172swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1172swap_checked : acceptsGraphIso
    (source (graph core1172) (root 8) 1 0) SmallGeFourSpectrum143.graph sourceMap1172swap=true := by decide +kernel
theorem fusedMap1172swap_checked : acceptsGraphIso
    (fused (graph core1172) (root 8) 1 0) SmallGeFourSpectrum144.graph fusedMap1172swap=true := by decide +kernel
theorem certified1172swap : Certified (graph core1172) (root 8) 1 0 :=
  of_native_maps core1172 SmallGeFourSpectrum143.graph SmallGeFourSpectrum144.graph
    sourceMap1172swap fusedMap1172swap sourceMap1172swap_checked fusedMap1172swap_checked
    DegreeOneSmallComparisons.comparison1172
#print axioms sourceMap1172swap_checked
#print axioms fusedMap1172swap_checked
#print axioms certified1172swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
