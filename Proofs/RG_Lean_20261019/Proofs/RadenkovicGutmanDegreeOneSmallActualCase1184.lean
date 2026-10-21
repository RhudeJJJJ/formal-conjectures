/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1184 : Family 8 := level8.get ⟨232,by decide⟩
def sourceMap1184 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1184 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1184_checked : acceptsGraphIso
    (source (graph core1184) (root 8) 0 1) SmallGeFourSpectrum168.graph sourceMap1184=true := by decide +kernel
theorem fusedMap1184_checked : acceptsGraphIso
    (fused (graph core1184) (root 8) 0 1) SmallGeFourSpectrum169.graph fusedMap1184=true := by decide +kernel
theorem certified1184 : Certified (graph core1184) (root 8) 0 1 :=
  of_native_maps core1184 SmallGeFourSpectrum168.graph SmallGeFourSpectrum169.graph
    sourceMap1184 fusedMap1184 sourceMap1184_checked fusedMap1184_checked
    DegreeOneSmallComparisons.comparison1184
#print axioms sourceMap1184_checked
#print axioms fusedMap1184_checked
#print axioms certified1184
def sourceMap1184swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1184swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1184swap_checked : acceptsGraphIso
    (source (graph core1184) (root 8) 1 0) SmallGeFourSpectrum168.graph sourceMap1184swap=true := by decide +kernel
theorem fusedMap1184swap_checked : acceptsGraphIso
    (fused (graph core1184) (root 8) 1 0) SmallGeFourSpectrum169.graph fusedMap1184swap=true := by decide +kernel
theorem certified1184swap : Certified (graph core1184) (root 8) 1 0 :=
  of_native_maps core1184 SmallGeFourSpectrum168.graph SmallGeFourSpectrum169.graph
    sourceMap1184swap fusedMap1184swap sourceMap1184swap_checked fusedMap1184swap_checked
    DegreeOneSmallComparisons.comparison1184
#print axioms sourceMap1184swap_checked
#print axioms fusedMap1184swap_checked
#print axioms certified1184swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
