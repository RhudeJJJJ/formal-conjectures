/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1731 : Family 9 := level9.get ⟨550,by decide⟩
def sourceMap1731 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1731 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1731_checked : acceptsGraphIso
    (source (graph core1731) (root 9) 0 0) DegreeOneSmallSpectrum839.graph sourceMap1731=true := by decide +kernel
theorem fusedMap1731_checked : acceptsGraphIso
    (fused (graph core1731) (root 9) 0 0) DegreeOneSmallSpectrum604.graph fusedMap1731=true := by decide +kernel
theorem certified1731 : Certified (graph core1731) (root 9) 0 0 :=
  of_native_maps core1731 DegreeOneSmallSpectrum839.graph DegreeOneSmallSpectrum604.graph
    sourceMap1731 fusedMap1731 sourceMap1731_checked fusedMap1731_checked
    DegreeOneSmallComparisons.comparison1731
#print axioms sourceMap1731_checked
#print axioms fusedMap1731_checked
#print axioms certified1731
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
