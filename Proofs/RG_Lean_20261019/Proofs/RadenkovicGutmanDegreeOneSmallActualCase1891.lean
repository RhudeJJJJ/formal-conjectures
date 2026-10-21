/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1891 : Family 10 := level10.get ⟨160,by decide⟩
def sourceMap1891 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1891 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1891_checked : acceptsGraphIso
    (source (graph core1891) (root 10) 0 0) DegreeOneSmallSpectrum1135.graph sourceMap1891=true := by decide +kernel
theorem fusedMap1891_checked : acceptsGraphIso
    (fused (graph core1891) (root 10) 0 0) DegreeOneSmallSpectrum955.graph fusedMap1891=true := by decide +kernel
theorem certified1891 : Certified (graph core1891) (root 10) 0 0 :=
  of_native_maps core1891 DegreeOneSmallSpectrum1135.graph DegreeOneSmallSpectrum955.graph
    sourceMap1891 fusedMap1891 sourceMap1891_checked fusedMap1891_checked
    DegreeOneSmallComparisons.comparison1891
#print axioms sourceMap1891_checked
#print axioms fusedMap1891_checked
#print axioms certified1891
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
