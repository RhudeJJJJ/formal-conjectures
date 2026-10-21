/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1954 : Family 10 := level10.get ⟨259,by decide⟩
def sourceMap1954 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap1954 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1954_checked : acceptsGraphIso
    (source (graph core1954) (root 10) 0 0) DegreeOneSmallSpectrum1186.graph sourceMap1954=true := by decide +kernel
theorem fusedMap1954_checked : acceptsGraphIso
    (fused (graph core1954) (root 10) 0 0) DegreeOneSmallSpectrum1288.graph fusedMap1954=true := by decide +kernel
theorem certified1954 : Certified (graph core1954) (root 10) 0 0 :=
  of_native_maps core1954 DegreeOneSmallSpectrum1186.graph DegreeOneSmallSpectrum1288.graph
    sourceMap1954 fusedMap1954 sourceMap1954_checked fusedMap1954_checked
    DegreeOneSmallComparisons.comparison1954
#print axioms sourceMap1954_checked
#print axioms fusedMap1954_checked
#print axioms certified1954
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
