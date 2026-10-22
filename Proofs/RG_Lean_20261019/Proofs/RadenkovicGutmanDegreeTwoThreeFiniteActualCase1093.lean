/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1093 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap1093 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap1093 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1093_checked : acceptsGraphIso
    (source (graph core1093) (root 7) 0 2) SmallGeFourSpectrum118.graph sourceMap1093=true := by decide +kernel
theorem fusedMap1093_checked : acceptsGraphIso
    (fused (graph core1093) (root 7) 0 2) SmallGeFourSpectrum121.graph fusedMap1093=true := by decide +kernel
theorem certified1093 : Certified (graph core1093) (root 7) 0 2 :=
  of_native_maps core1093 SmallGeFourSpectrum118.graph SmallGeFourSpectrum121.graph
    sourceMap1093 fusedMap1093 sourceMap1093_checked fusedMap1093_checked
    DegreeTwoThreeFiniteComparisons.comparison1093
#print axioms sourceMap1093_checked
#print axioms fusedMap1093_checked
#print axioms certified1093
def sourceMap1093swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap1093swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1093swap_checked : acceptsGraphIso
    (source (graph core1093) (root 7) 2 0) SmallGeFourSpectrum118.graph sourceMap1093swap=true := by decide +kernel
theorem fusedMap1093swap_checked : acceptsGraphIso
    (fused (graph core1093) (root 7) 2 0) SmallGeFourSpectrum121.graph fusedMap1093swap=true := by decide +kernel
theorem certified1093swap : Certified (graph core1093) (root 7) 2 0 :=
  of_native_maps core1093 SmallGeFourSpectrum118.graph SmallGeFourSpectrum121.graph
    sourceMap1093swap fusedMap1093swap sourceMap1093swap_checked fusedMap1093swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1093
#print axioms sourceMap1093swap_checked
#print axioms fusedMap1093swap_checked
#print axioms certified1093swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
