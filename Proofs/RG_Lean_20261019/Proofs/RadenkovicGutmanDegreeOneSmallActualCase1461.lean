/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1461 : Family 9 := level9.get ⟨200,by decide⟩
def sourceMap1461 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1461 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1461_checked : acceptsGraphIso
    (source (graph core1461) (root 9) 0 0) SmallGeFourSpectrum157.graph sourceMap1461=true := by decide +kernel
theorem fusedMap1461_checked : acceptsGraphIso
    (fused (graph core1461) (root 9) 0 0) SmallGeFourSpectrum099.graph fusedMap1461=true := by decide +kernel
theorem certified1461 : Certified (graph core1461) (root 9) 0 0 :=
  of_native_maps core1461 SmallGeFourSpectrum157.graph SmallGeFourSpectrum099.graph
    sourceMap1461 fusedMap1461 sourceMap1461_checked fusedMap1461_checked
    DegreeOneSmallComparisons.comparison1461
#print axioms sourceMap1461_checked
#print axioms fusedMap1461_checked
#print axioms certified1461
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
