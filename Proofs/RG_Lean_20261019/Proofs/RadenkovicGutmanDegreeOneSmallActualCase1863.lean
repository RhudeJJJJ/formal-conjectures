/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1863 : Family 10 := level10.get ⟨122,by decide⟩
def sourceMap1863 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1863 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1863_checked : acceptsGraphIso
    (source (graph core1863) (root 10) 0 0) DegreeOneSmallSpectrum1282.graph sourceMap1863=true := by decide +kernel
theorem fusedMap1863_checked : acceptsGraphIso
    (fused (graph core1863) (root 10) 0 0) DegreeOneSmallSpectrum948.graph fusedMap1863=true := by decide +kernel
theorem certified1863 : Certified (graph core1863) (root 10) 0 0 :=
  of_native_maps core1863 DegreeOneSmallSpectrum1282.graph DegreeOneSmallSpectrum948.graph
    sourceMap1863 fusedMap1863 sourceMap1863_checked fusedMap1863_checked
    DegreeOneSmallComparisons.comparison1863
#print axioms sourceMap1863_checked
#print axioms fusedMap1863_checked
#print axioms certified1863
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
