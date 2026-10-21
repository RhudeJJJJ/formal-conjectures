/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1675 : Family 9 := level9.get ⟨438,by decide⟩
def sourceMap1675 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1675 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1675_checked : acceptsGraphIso
    (source (graph core1675) (root 9) 0 0) SmallGeFourSpectrum158.graph sourceMap1675=true := by decide +kernel
theorem fusedMap1675_checked : acceptsGraphIso
    (fused (graph core1675) (root 9) 0 0) SmallGeFourSpectrum180.graph fusedMap1675=true := by decide +kernel
theorem certified1675 : Certified (graph core1675) (root 9) 0 0 :=
  of_native_maps core1675 SmallGeFourSpectrum158.graph SmallGeFourSpectrum180.graph
    sourceMap1675 fusedMap1675 sourceMap1675_checked fusedMap1675_checked
    DegreeOneSmallComparisons.comparison1675
#print axioms sourceMap1675_checked
#print axioms fusedMap1675_checked
#print axioms certified1675
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
