/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1789 : Family 10 := level10.get ⟨24,by decide⟩
def sourceMap1789 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1789 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1789_checked : acceptsGraphIso
    (source (graph core1789) (root 10) 0 0) DegreeOneSmallSpectrum876.graph sourceMap1789=true := by decide +kernel
theorem fusedMap1789_checked : acceptsGraphIso
    (fused (graph core1789) (root 10) 0 0) DegreeOneSmallSpectrum940.graph fusedMap1789=true := by decide +kernel
theorem certified1789 : Certified (graph core1789) (root 10) 0 0 :=
  of_native_maps core1789 DegreeOneSmallSpectrum876.graph DegreeOneSmallSpectrum940.graph
    sourceMap1789 fusedMap1789 sourceMap1789_checked fusedMap1789_checked
    DegreeOneSmallComparisons.comparison1789
#print axioms sourceMap1789_checked
#print axioms fusedMap1789_checked
#print axioms certified1789
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
