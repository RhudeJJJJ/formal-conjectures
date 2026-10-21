/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1080 : Family 8 := level8.get ⟨141,by decide⟩
def sourceMap1080 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1080 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1080_checked : acceptsGraphIso
    (source (graph core1080) (root 8) 0 1) SmallGeFourSpectrum182.graph sourceMap1080=true := by decide +kernel
theorem fusedMap1080_checked : acceptsGraphIso
    (fused (graph core1080) (root 8) 0 1) SmallGeFourSpectrum100.graph fusedMap1080=true := by decide +kernel
theorem certified1080 : Certified (graph core1080) (root 8) 0 1 :=
  of_native_maps core1080 SmallGeFourSpectrum182.graph SmallGeFourSpectrum100.graph
    sourceMap1080 fusedMap1080 sourceMap1080_checked fusedMap1080_checked
    DegreeOneSmallComparisons.comparison1080
#print axioms sourceMap1080_checked
#print axioms fusedMap1080_checked
#print axioms certified1080
def sourceMap1080swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1080swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1080swap_checked : acceptsGraphIso
    (source (graph core1080) (root 8) 1 0) SmallGeFourSpectrum182.graph sourceMap1080swap=true := by decide +kernel
theorem fusedMap1080swap_checked : acceptsGraphIso
    (fused (graph core1080) (root 8) 1 0) SmallGeFourSpectrum100.graph fusedMap1080swap=true := by decide +kernel
theorem certified1080swap : Certified (graph core1080) (root 8) 1 0 :=
  of_native_maps core1080 SmallGeFourSpectrum182.graph SmallGeFourSpectrum100.graph
    sourceMap1080swap fusedMap1080swap sourceMap1080swap_checked fusedMap1080swap_checked
    DegreeOneSmallComparisons.comparison1080
#print axioms sourceMap1080swap_checked
#print axioms fusedMap1080swap_checked
#print axioms certified1080swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
