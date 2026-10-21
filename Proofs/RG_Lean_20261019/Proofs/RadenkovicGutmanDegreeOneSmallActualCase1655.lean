/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1655 : Family 9 := level9.get ⟨415,by decide⟩
def sourceMap1655 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1655 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1655_checked : acceptsGraphIso
    (source (graph core1655) (root 9) 0 0) SmallGeFourSpectrum155.graph sourceMap1655=true := by decide +kernel
theorem fusedMap1655_checked : acceptsGraphIso
    (fused (graph core1655) (root 9) 0 0) SmallGeFourSpectrum166.graph fusedMap1655=true := by decide +kernel
theorem certified1655 : Certified (graph core1655) (root 9) 0 0 :=
  of_native_maps core1655 SmallGeFourSpectrum155.graph SmallGeFourSpectrum166.graph
    sourceMap1655 fusedMap1655 sourceMap1655_checked fusedMap1655_checked
    DegreeOneSmallComparisons.comparison1655
#print axioms sourceMap1655_checked
#print axioms fusedMap1655_checked
#print axioms certified1655
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
