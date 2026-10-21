/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1135 : Family 8 := level8.get ⟨188,by decide⟩
def sourceMap1135 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (sourceLabel 8 0 0 v)
def fusedMap1135 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1135_checked : acceptsGraphIso
    (source (graph core1135) (root 8) 0 0) SmallGeFourSpectrum073.graph sourceMap1135=true := by decide +kernel
theorem fusedMap1135_checked : acceptsGraphIso
    (fused (graph core1135) (root 8) 0 0) SmallGeFourSpectrum040.graph fusedMap1135=true := by decide +kernel
theorem certified1135 : Certified (graph core1135) (root 8) 0 0 :=
  of_native_maps core1135 SmallGeFourSpectrum073.graph SmallGeFourSpectrum040.graph
    sourceMap1135 fusedMap1135 sourceMap1135_checked fusedMap1135_checked
    DegreeOneSmallComparisons.comparison1135
#print axioms sourceMap1135_checked
#print axioms fusedMap1135_checked
#print axioms certified1135
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
