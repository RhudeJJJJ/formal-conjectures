/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1788 : Family 10 := level10.get ⟨23,by decide⟩
def sourceMap1788 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1788 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1788_checked : acceptsGraphIso
    (source (graph core1788) (root 10) 0 0) DegreeOneSmallSpectrum884.graph sourceMap1788=true := by decide +kernel
theorem fusedMap1788_checked : acceptsGraphIso
    (fused (graph core1788) (root 10) 0 0) DegreeOneSmallSpectrum943.graph fusedMap1788=true := by decide +kernel
theorem certified1788 : Certified (graph core1788) (root 10) 0 0 :=
  of_native_maps core1788 DegreeOneSmallSpectrum884.graph DegreeOneSmallSpectrum943.graph
    sourceMap1788 fusedMap1788 sourceMap1788_checked fusedMap1788_checked
    DegreeOneSmallComparisons.comparison1788
#print axioms sourceMap1788_checked
#print axioms fusedMap1788_checked
#print axioms certified1788
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
