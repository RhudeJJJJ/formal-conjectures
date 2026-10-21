/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1709 : Family 9 := level9.get ⟨491,by decide⟩
def sourceMap1709 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,9,10,11,1,2,3,4,5,7,8] (sourceLabel 9 0 0 v)
def fusedMap1709 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1709_checked : acceptsGraphIso
    (source (graph core1709) (root 9) 0 0) DegreeOneSmallSpectrum604.graph sourceMap1709=true := by decide +kernel
theorem fusedMap1709_checked : acceptsGraphIso
    (fused (graph core1709) (root 9) 0 0) DegreeOneSmallSpectrum824.graph fusedMap1709=true := by decide +kernel
theorem certified1709 : Certified (graph core1709) (root 9) 0 0 :=
  of_native_maps core1709 DegreeOneSmallSpectrum604.graph DegreeOneSmallSpectrum824.graph
    sourceMap1709 fusedMap1709 sourceMap1709_checked fusedMap1709_checked
    DegreeOneSmallComparisons.comparison1709
#print axioms sourceMap1709_checked
#print axioms fusedMap1709_checked
#print axioms certified1709
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
