/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1901 : Family 10 := level10.get ⟨178,by decide⟩
def sourceMap1901 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,6,7,8,4,5] (sourceLabel 10 0 0 v)
def fusedMap1901 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1901_checked : acceptsGraphIso
    (source (graph core1901) (root 10) 0 0) DegreeOneSmallSpectrum1088.graph sourceMap1901=true := by decide +kernel
theorem fusedMap1901_checked : acceptsGraphIso
    (fused (graph core1901) (root 10) 0 0) DegreeOneSmallSpectrum946.graph fusedMap1901=true := by decide +kernel
theorem certified1901 : Certified (graph core1901) (root 10) 0 0 :=
  of_native_maps core1901 DegreeOneSmallSpectrum1088.graph DegreeOneSmallSpectrum946.graph
    sourceMap1901 fusedMap1901 sourceMap1901_checked fusedMap1901_checked
    DegreeOneSmallComparisons.comparison1901
#print axioms sourceMap1901_checked
#print axioms fusedMap1901_checked
#print axioms certified1901
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
