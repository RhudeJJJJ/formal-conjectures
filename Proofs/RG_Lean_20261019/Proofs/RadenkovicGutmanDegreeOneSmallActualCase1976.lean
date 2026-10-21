/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1976 : Family 10 := level10.get ⟨296,by decide⟩
def sourceMap1976 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1976 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1976_checked : acceptsGraphIso
    (source (graph core1976) (root 10) 0 0) DegreeOneSmallSpectrum1219.graph sourceMap1976=true := by decide +kernel
theorem fusedMap1976_checked : acceptsGraphIso
    (fused (graph core1976) (root 10) 0 0) DegreeOneSmallSpectrum1348.graph fusedMap1976=true := by decide +kernel
theorem certified1976 : Certified (graph core1976) (root 10) 0 0 :=
  of_native_maps core1976 DegreeOneSmallSpectrum1219.graph DegreeOneSmallSpectrum1348.graph
    sourceMap1976 fusedMap1976 sourceMap1976_checked fusedMap1976_checked
    DegreeOneSmallComparisons.comparison1976
#print axioms sourceMap1976_checked
#print axioms fusedMap1976_checked
#print axioms certified1976
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
