/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1951 : Family 10 := level10.get ⟨252,by decide⟩
def sourceMap1951 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1951 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1951_checked : acceptsGraphIso
    (source (graph core1951) (root 10) 0 0) DegreeOneSmallSpectrum1149.graph sourceMap1951=true := by decide +kernel
theorem fusedMap1951_checked : acceptsGraphIso
    (fused (graph core1951) (root 10) 0 0) DegreeOneSmallSpectrum1245.graph fusedMap1951=true := by decide +kernel
theorem certified1951 : Certified (graph core1951) (root 10) 0 0 :=
  of_native_maps core1951 DegreeOneSmallSpectrum1149.graph DegreeOneSmallSpectrum1245.graph
    sourceMap1951 fusedMap1951 sourceMap1951_checked fusedMap1951_checked
    DegreeOneSmallComparisons.comparison1951
#print axioms sourceMap1951_checked
#print axioms fusedMap1951_checked
#print axioms certified1951
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
