/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1921 : Family 10 := level10.get ⟨210,by decide⟩
def sourceMap1921 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1921 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1921_checked : acceptsGraphIso
    (source (graph core1921) (root 10) 0 0) DegreeOneSmallSpectrum1060.graph sourceMap1921=true := by decide +kernel
theorem fusedMap1921_checked : acceptsGraphIso
    (fused (graph core1921) (root 10) 0 0) DegreeOneSmallSpectrum1077.graph fusedMap1921=true := by decide +kernel
theorem certified1921 : Certified (graph core1921) (root 10) 0 0 :=
  of_native_maps core1921 DegreeOneSmallSpectrum1060.graph DegreeOneSmallSpectrum1077.graph
    sourceMap1921 fusedMap1921 sourceMap1921_checked fusedMap1921_checked
    DegreeOneSmallComparisons.comparison1921
#print axioms sourceMap1921_checked
#print axioms fusedMap1921_checked
#print axioms certified1921
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
