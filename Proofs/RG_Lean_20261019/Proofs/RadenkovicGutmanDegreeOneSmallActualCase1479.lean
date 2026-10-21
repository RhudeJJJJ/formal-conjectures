/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1479 : Family 9 := level9.get ⟨214,by decide⟩
def sourceMap1479 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1479 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1479_checked : acceptsGraphIso
    (source (graph core1479) (root 9) 0 0) SmallGeFourSpectrum160.graph sourceMap1479=true := by decide +kernel
theorem fusedMap1479_checked : acceptsGraphIso
    (fused (graph core1479) (root 9) 0 0) SmallGeFourSpectrum101.graph fusedMap1479=true := by decide +kernel
theorem certified1479 : Certified (graph core1479) (root 9) 0 0 :=
  of_native_maps core1479 SmallGeFourSpectrum160.graph SmallGeFourSpectrum101.graph
    sourceMap1479 fusedMap1479 sourceMap1479_checked fusedMap1479_checked
    DegreeOneSmallComparisons.comparison1479
#print axioms sourceMap1479_checked
#print axioms fusedMap1479_checked
#print axioms certified1479
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
