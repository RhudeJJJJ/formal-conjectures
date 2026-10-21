/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1867 : Family 10 := level10.get ⟨127,by decide⟩
def sourceMap1867 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1867 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1867_checked : acceptsGraphIso
    (source (graph core1867) (root 10) 0 0) DegreeOneSmallSpectrum1285.graph sourceMap1867=true := by decide +kernel
theorem fusedMap1867_checked : acceptsGraphIso
    (fused (graph core1867) (root 10) 0 0) DegreeOneSmallSpectrum953.graph fusedMap1867=true := by decide +kernel
theorem certified1867 : Certified (graph core1867) (root 10) 0 0 :=
  of_native_maps core1867 DegreeOneSmallSpectrum1285.graph DegreeOneSmallSpectrum953.graph
    sourceMap1867 fusedMap1867 sourceMap1867_checked fusedMap1867_checked
    DegreeOneSmallComparisons.comparison1867
#print axioms sourceMap1867_checked
#print axioms fusedMap1867_checked
#print axioms certified1867
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
