/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1796 : Family 10 := level10.get ⟨33,by decide⟩
def sourceMap1796 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1796 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1796_checked : acceptsGraphIso
    (source (graph core1796) (root 10) 0 0) DegreeOneSmallSpectrum905.graph sourceMap1796=true := by decide +kernel
theorem fusedMap1796_checked : acceptsGraphIso
    (fused (graph core1796) (root 10) 0 0) DegreeOneSmallSpectrum971.graph fusedMap1796=true := by decide +kernel
theorem certified1796 : Certified (graph core1796) (root 10) 0 0 :=
  of_native_maps core1796 DegreeOneSmallSpectrum905.graph DegreeOneSmallSpectrum971.graph
    sourceMap1796 fusedMap1796 sourceMap1796_checked fusedMap1796_checked
    DegreeOneSmallComparisons.comparison1796
#print axioms sourceMap1796_checked
#print axioms fusedMap1796_checked
#print axioms certified1796
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
