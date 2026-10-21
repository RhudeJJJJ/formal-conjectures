/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1949 : Family 10 := level10.get ⟨250,by decide⟩
def sourceMap1949 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1949 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1949_checked : acceptsGraphIso
    (source (graph core1949) (root 10) 0 0) DegreeOneSmallSpectrum1202.graph sourceMap1949=true := by decide +kernel
theorem fusedMap1949_checked : acceptsGraphIso
    (fused (graph core1949) (root 10) 0 0) DegreeOneSmallSpectrum1246.graph fusedMap1949=true := by decide +kernel
theorem certified1949 : Certified (graph core1949) (root 10) 0 0 :=
  of_native_maps core1949 DegreeOneSmallSpectrum1202.graph DegreeOneSmallSpectrum1246.graph
    sourceMap1949 fusedMap1949 sourceMap1949_checked fusedMap1949_checked
    DegreeOneSmallComparisons.comparison1949
#print axioms sourceMap1949_checked
#print axioms fusedMap1949_checked
#print axioms certified1949
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
