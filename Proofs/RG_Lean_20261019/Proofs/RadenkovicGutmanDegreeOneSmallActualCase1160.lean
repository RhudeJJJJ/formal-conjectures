/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1160 : Family 8 := level8.get ⟨199,by decide⟩
def sourceMap1160 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1160 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1160_checked : acceptsGraphIso
    (source (graph core1160) (root 8) 0 1) DegreeOneSmallSpectrum643.graph sourceMap1160=true := by decide +kernel
theorem fusedMap1160_checked : acceptsGraphIso
    (fused (graph core1160) (root 8) 0 1) SmallGeFourSpectrum133.graph fusedMap1160=true := by decide +kernel
theorem certified1160 : Certified (graph core1160) (root 8) 0 1 :=
  of_native_maps core1160 DegreeOneSmallSpectrum643.graph SmallGeFourSpectrum133.graph
    sourceMap1160 fusedMap1160 sourceMap1160_checked fusedMap1160_checked
    DegreeOneSmallComparisons.comparison1160
#print axioms sourceMap1160_checked
#print axioms fusedMap1160_checked
#print axioms certified1160
def sourceMap1160swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1160swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1160swap_checked : acceptsGraphIso
    (source (graph core1160) (root 8) 1 0) DegreeOneSmallSpectrum643.graph sourceMap1160swap=true := by decide +kernel
theorem fusedMap1160swap_checked : acceptsGraphIso
    (fused (graph core1160) (root 8) 1 0) SmallGeFourSpectrum133.graph fusedMap1160swap=true := by decide +kernel
theorem certified1160swap : Certified (graph core1160) (root 8) 1 0 :=
  of_native_maps core1160 DegreeOneSmallSpectrum643.graph SmallGeFourSpectrum133.graph
    sourceMap1160swap fusedMap1160swap sourceMap1160swap_checked fusedMap1160swap_checked
    DegreeOneSmallComparisons.comparison1160
#print axioms sourceMap1160swap_checked
#print axioms fusedMap1160swap_checked
#print axioms certified1160swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
