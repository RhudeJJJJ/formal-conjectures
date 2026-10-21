/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1018 : Family 8 := level8.get ⟨108,by decide⟩
def sourceMap1018 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1018 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1018_checked : acceptsGraphIso
    (source (graph core1018) (root 8) 1 1) DegreeOneSmallSpectrum1717.graph sourceMap1018=true := by decide +kernel
theorem fusedMap1018_checked : acceptsGraphIso
    (fused (graph core1018) (root 8) 1 1) DegreeOneSmallSpectrum1088.graph fusedMap1018=true := by decide +kernel
theorem certified1018 : Certified (graph core1018) (root 8) 1 1 :=
  of_native_maps core1018 DegreeOneSmallSpectrum1717.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1018 fusedMap1018 sourceMap1018_checked fusedMap1018_checked
    DegreeOneSmallComparisons.comparison1018
#print axioms sourceMap1018_checked
#print axioms fusedMap1018_checked
#print axioms certified1018
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
