/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1818 : Family 10 := level10.get ⟨62,by decide⟩
def sourceMap1818 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1818 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1818_checked : acceptsGraphIso
    (source (graph core1818) (root 10) 0 0) DegreeOneSmallSpectrum1150.graph sourceMap1818=true := by decide +kernel
theorem fusedMap1818_checked : acceptsGraphIso
    (fused (graph core1818) (root 10) 0 0) DegreeOneSmallSpectrum873.graph fusedMap1818=true := by decide +kernel
theorem certified1818 : Certified (graph core1818) (root 10) 0 0 :=
  of_native_maps core1818 DegreeOneSmallSpectrum1150.graph DegreeOneSmallSpectrum873.graph
    sourceMap1818 fusedMap1818 sourceMap1818_checked fusedMap1818_checked
    DegreeOneSmallComparisons.comparison1818
#print axioms sourceMap1818_checked
#print axioms fusedMap1818_checked
#print axioms certified1818
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
