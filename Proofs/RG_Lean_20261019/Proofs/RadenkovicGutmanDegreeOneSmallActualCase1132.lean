/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1132 : Family 8 := level8.get ⟨171,by decide⟩
def sourceMap1132 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1132 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1132_checked : acceptsGraphIso
    (source (graph core1132) (root 8) 0 1) SmallGeFourSpectrum191.graph sourceMap1132=true := by decide +kernel
theorem fusedMap1132_checked : acceptsGraphIso
    (fused (graph core1132) (root 8) 0 1) SmallGeFourSpectrum108.graph fusedMap1132=true := by decide +kernel
theorem certified1132 : Certified (graph core1132) (root 8) 0 1 :=
  of_native_maps core1132 SmallGeFourSpectrum191.graph SmallGeFourSpectrum108.graph
    sourceMap1132 fusedMap1132 sourceMap1132_checked fusedMap1132_checked
    DegreeOneSmallComparisons.comparison1132
#print axioms sourceMap1132_checked
#print axioms fusedMap1132_checked
#print axioms certified1132
def sourceMap1132swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1132swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1132swap_checked : acceptsGraphIso
    (source (graph core1132) (root 8) 1 0) SmallGeFourSpectrum191.graph sourceMap1132swap=true := by decide +kernel
theorem fusedMap1132swap_checked : acceptsGraphIso
    (fused (graph core1132) (root 8) 1 0) SmallGeFourSpectrum108.graph fusedMap1132swap=true := by decide +kernel
theorem certified1132swap : Certified (graph core1132) (root 8) 1 0 :=
  of_native_maps core1132 SmallGeFourSpectrum191.graph SmallGeFourSpectrum108.graph
    sourceMap1132swap fusedMap1132swap sourceMap1132swap_checked fusedMap1132swap_checked
    DegreeOneSmallComparisons.comparison1132
#print axioms sourceMap1132swap_checked
#print axioms fusedMap1132swap_checked
#print axioms certified1132swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
