/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1980 : Family 10 := level10.get ⟨304,by decide⟩
def sourceMap1980 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1980 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1980_checked : acceptsGraphIso
    (source (graph core1980) (root 10) 0 0) DegreeOneSmallSpectrum1258.graph sourceMap1980=true := by decide +kernel
theorem fusedMap1980_checked : acceptsGraphIso
    (fused (graph core1980) (root 10) 0 0) DegreeOneSmallSpectrum1353.graph fusedMap1980=true := by decide +kernel
theorem certified1980 : Certified (graph core1980) (root 10) 0 0 :=
  of_native_maps core1980 DegreeOneSmallSpectrum1258.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1980 fusedMap1980 sourceMap1980_checked fusedMap1980_checked
    DegreeOneSmallComparisons.comparison1980
#print axioms sourceMap1980_checked
#print axioms fusedMap1980_checked
#print axioms certified1980
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
