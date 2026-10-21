/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1859 : Family 10 := level10.get ⟨115,by decide⟩
def sourceMap1859 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1859 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1859_checked : acceptsGraphIso
    (source (graph core1859) (root 10) 0 0) DegreeOneSmallSpectrum1131.graph sourceMap1859=true := by decide +kernel
theorem fusedMap1859_checked : acceptsGraphIso
    (fused (graph core1859) (root 10) 0 0) DegreeOneSmallSpectrum938.graph fusedMap1859=true := by decide +kernel
theorem certified1859 : Certified (graph core1859) (root 10) 0 0 :=
  of_native_maps core1859 DegreeOneSmallSpectrum1131.graph DegreeOneSmallSpectrum938.graph
    sourceMap1859 fusedMap1859 sourceMap1859_checked fusedMap1859_checked
    DegreeOneSmallComparisons.comparison1859
#print axioms sourceMap1859_checked
#print axioms fusedMap1859_checked
#print axioms certified1859
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
