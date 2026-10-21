/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1192 : Family 8 := level8.get ⟨264,by decide⟩
def sourceMap1192 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1192 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1192_checked : acceptsGraphIso
    (source (graph core1192) (root 8) 0 1) SmallGeFourSpectrum202.graph sourceMap1192=true := by decide +kernel
theorem fusedMap1192_checked : acceptsGraphIso
    (fused (graph core1192) (root 8) 0 1) SmallGeFourSpectrum112.graph fusedMap1192=true := by decide +kernel
theorem certified1192 : Certified (graph core1192) (root 8) 0 1 :=
  of_native_maps core1192 SmallGeFourSpectrum202.graph SmallGeFourSpectrum112.graph
    sourceMap1192 fusedMap1192 sourceMap1192_checked fusedMap1192_checked
    DegreeOneSmallComparisons.comparison1192
#print axioms sourceMap1192_checked
#print axioms fusedMap1192_checked
#print axioms certified1192
def sourceMap1192swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1192swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1192swap_checked : acceptsGraphIso
    (source (graph core1192) (root 8) 1 0) SmallGeFourSpectrum202.graph sourceMap1192swap=true := by decide +kernel
theorem fusedMap1192swap_checked : acceptsGraphIso
    (fused (graph core1192) (root 8) 1 0) SmallGeFourSpectrum112.graph fusedMap1192swap=true := by decide +kernel
theorem certified1192swap : Certified (graph core1192) (root 8) 1 0 :=
  of_native_maps core1192 SmallGeFourSpectrum202.graph SmallGeFourSpectrum112.graph
    sourceMap1192swap fusedMap1192swap sourceMap1192swap_checked fusedMap1192swap_checked
    DegreeOneSmallComparisons.comparison1192
#print axioms sourceMap1192swap_checked
#print axioms fusedMap1192swap_checked
#print axioms certified1192swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
