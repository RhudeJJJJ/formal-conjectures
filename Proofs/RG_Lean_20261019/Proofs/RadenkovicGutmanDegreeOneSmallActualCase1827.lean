/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1827 : Family 10 := level10.get ⟨73,by decide⟩
def sourceMap1827 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1827 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1827_checked : acceptsGraphIso
    (source (graph core1827) (root 10) 0 0) DegreeOneSmallSpectrum1248.graph sourceMap1827=true := by decide +kernel
theorem fusedMap1827_checked : acceptsGraphIso
    (fused (graph core1827) (root 10) 0 0) DegreeOneSmallSpectrum888.graph fusedMap1827=true := by decide +kernel
theorem certified1827 : Certified (graph core1827) (root 10) 0 0 :=
  of_native_maps core1827 DegreeOneSmallSpectrum1248.graph DegreeOneSmallSpectrum888.graph
    sourceMap1827 fusedMap1827 sourceMap1827_checked fusedMap1827_checked
    DegreeOneSmallComparisons.comparison1827
#print axioms sourceMap1827_checked
#print axioms fusedMap1827_checked
#print axioms certified1827
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
