/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1140 : Family 8 := level8.get ⟨189,by decide⟩
def sourceMap1140 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1140 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1140_checked : acceptsGraphIso
    (source (graph core1140) (root 8) 0 1) SmallGeFourSpectrum120.graph sourceMap1140=true := by decide +kernel
theorem fusedMap1140_checked : acceptsGraphIso
    (fused (graph core1140) (root 8) 0 1) SmallGeFourSpectrum121.graph fusedMap1140=true := by decide +kernel
theorem certified1140 : Certified (graph core1140) (root 8) 0 1 :=
  of_native_maps core1140 SmallGeFourSpectrum120.graph SmallGeFourSpectrum121.graph
    sourceMap1140 fusedMap1140 sourceMap1140_checked fusedMap1140_checked
    DegreeOneSmallComparisons.comparison1140
#print axioms sourceMap1140_checked
#print axioms fusedMap1140_checked
#print axioms certified1140
def sourceMap1140swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1140swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1140swap_checked : acceptsGraphIso
    (source (graph core1140) (root 8) 1 0) SmallGeFourSpectrum120.graph sourceMap1140swap=true := by decide +kernel
theorem fusedMap1140swap_checked : acceptsGraphIso
    (fused (graph core1140) (root 8) 1 0) SmallGeFourSpectrum121.graph fusedMap1140swap=true := by decide +kernel
theorem certified1140swap : Certified (graph core1140) (root 8) 1 0 :=
  of_native_maps core1140 SmallGeFourSpectrum120.graph SmallGeFourSpectrum121.graph
    sourceMap1140swap fusedMap1140swap sourceMap1140swap_checked fusedMap1140swap_checked
    DegreeOneSmallComparisons.comparison1140
#print axioms sourceMap1140swap_checked
#print axioms fusedMap1140swap_checked
#print axioms certified1140swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
