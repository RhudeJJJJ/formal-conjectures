/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1876 : Family 10 := level10.get ⟨138,by decide⟩
def sourceMap1876 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1876 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1876_checked : acceptsGraphIso
    (source (graph core1876) (root 10) 0 0) DegreeOneSmallSpectrum1157.graph sourceMap1876=true := by decide +kernel
theorem fusedMap1876_checked : acceptsGraphIso
    (fused (graph core1876) (root 10) 0 0) DegreeOneSmallSpectrum959.graph fusedMap1876=true := by decide +kernel
theorem certified1876 : Certified (graph core1876) (root 10) 0 0 :=
  of_native_maps core1876 DegreeOneSmallSpectrum1157.graph DegreeOneSmallSpectrum959.graph
    sourceMap1876 fusedMap1876 sourceMap1876_checked fusedMap1876_checked
    DegreeOneSmallComparisons.comparison1876
#print axioms sourceMap1876_checked
#print axioms fusedMap1876_checked
#print axioms certified1876
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
