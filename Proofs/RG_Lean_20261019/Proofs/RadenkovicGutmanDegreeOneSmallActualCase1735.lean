/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1735 : Family 9 := level9.get ⟨553,by decide⟩
def sourceMap1735 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1735 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1735_checked : acceptsGraphIso
    (source (graph core1735) (root 9) 0 0) DegreeOneSmallSpectrum841.graph sourceMap1735=true := by decide +kernel
theorem fusedMap1735_checked : acceptsGraphIso
    (fused (graph core1735) (root 9) 0 0) SmallGeFourSpectrum129.graph fusedMap1735=true := by decide +kernel
theorem certified1735 : Certified (graph core1735) (root 9) 0 0 :=
  of_native_maps core1735 DegreeOneSmallSpectrum841.graph SmallGeFourSpectrum129.graph
    sourceMap1735 fusedMap1735 sourceMap1735_checked fusedMap1735_checked
    DegreeOneSmallComparisons.comparison1735
#print axioms sourceMap1735_checked
#print axioms fusedMap1735_checked
#print axioms certified1735
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
