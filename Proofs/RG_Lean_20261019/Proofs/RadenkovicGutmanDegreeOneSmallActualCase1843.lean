/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1843 : Family 10 := level10.get ⟨95,by decide⟩
def sourceMap1843 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1843 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1843_checked : acceptsGraphIso
    (source (graph core1843) (root 10) 0 0) DegreeOneSmallSpectrum1264.graph sourceMap1843=true := by decide +kernel
theorem fusedMap1843_checked : acceptsGraphIso
    (fused (graph core1843) (root 10) 0 0) DegreeOneSmallSpectrum918.graph fusedMap1843=true := by decide +kernel
theorem certified1843 : Certified (graph core1843) (root 10) 0 0 :=
  of_native_maps core1843 DegreeOneSmallSpectrum1264.graph DegreeOneSmallSpectrum918.graph
    sourceMap1843 fusedMap1843 sourceMap1843_checked fusedMap1843_checked
    DegreeOneSmallComparisons.comparison1843
#print axioms sourceMap1843_checked
#print axioms fusedMap1843_checked
#print axioms certified1843
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
