/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1128 : Family 8 := level8.get ⟨167,by decide⟩
def sourceMap1128 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap1128 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1128_checked : acceptsGraphIso
    (source (graph core1128) (root 8) 0 1) SmallGeFourSpectrum190.graph sourceMap1128=true := by decide +kernel
theorem fusedMap1128_checked : acceptsGraphIso
    (fused (graph core1128) (root 8) 0 1) SmallGeFourSpectrum107.graph fusedMap1128=true := by decide +kernel
theorem certified1128 : Certified (graph core1128) (root 8) 0 1 :=
  of_native_maps core1128 SmallGeFourSpectrum190.graph SmallGeFourSpectrum107.graph
    sourceMap1128 fusedMap1128 sourceMap1128_checked fusedMap1128_checked
    DegreeOneSmallComparisons.comparison1128
#print axioms sourceMap1128_checked
#print axioms fusedMap1128_checked
#print axioms certified1128
def sourceMap1128swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap1128swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1128swap_checked : acceptsGraphIso
    (source (graph core1128) (root 8) 1 0) SmallGeFourSpectrum190.graph sourceMap1128swap=true := by decide +kernel
theorem fusedMap1128swap_checked : acceptsGraphIso
    (fused (graph core1128) (root 8) 1 0) SmallGeFourSpectrum107.graph fusedMap1128swap=true := by decide +kernel
theorem certified1128swap : Certified (graph core1128) (root 8) 1 0 :=
  of_native_maps core1128 SmallGeFourSpectrum190.graph SmallGeFourSpectrum107.graph
    sourceMap1128swap fusedMap1128swap sourceMap1128swap_checked fusedMap1128swap_checked
    DegreeOneSmallComparisons.comparison1128
#print axioms sourceMap1128swap_checked
#print axioms fusedMap1128swap_checked
#print axioms certified1128swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
