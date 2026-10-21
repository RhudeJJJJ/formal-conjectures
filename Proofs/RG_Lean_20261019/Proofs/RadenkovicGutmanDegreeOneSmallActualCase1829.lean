/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1829 : Family 10 := level10.get ⟨75,by decide⟩
def sourceMap1829 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1829 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1829_checked : acceptsGraphIso
    (source (graph core1829) (root 10) 0 0) DegreeOneSmallSpectrum1228.graph sourceMap1829=true := by decide +kernel
theorem fusedMap1829_checked : acceptsGraphIso
    (fused (graph core1829) (root 10) 0 0) DegreeOneSmallSpectrum893.graph fusedMap1829=true := by decide +kernel
theorem certified1829 : Certified (graph core1829) (root 10) 0 0 :=
  of_native_maps core1829 DegreeOneSmallSpectrum1228.graph DegreeOneSmallSpectrum893.graph
    sourceMap1829 fusedMap1829 sourceMap1829_checked fusedMap1829_checked
    DegreeOneSmallComparisons.comparison1829
#print axioms sourceMap1829_checked
#print axioms fusedMap1829_checked
#print axioms certified1829
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
