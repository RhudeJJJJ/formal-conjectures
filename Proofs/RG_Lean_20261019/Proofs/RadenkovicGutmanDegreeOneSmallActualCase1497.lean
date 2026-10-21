/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1497 : Family 9 := level9.get ⟨228,by decide⟩
def sourceMap1497 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1497 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1497_checked : acceptsGraphIso
    (source (graph core1497) (root 9) 0 0) DegreeOneSmallSpectrum763.graph sourceMap1497=true := by decide +kernel
theorem fusedMap1497_checked : acceptsGraphIso
    (fused (graph core1497) (root 9) 0 0) DegreeOneSmallSpectrum537.graph fusedMap1497=true := by decide +kernel
theorem certified1497 : Certified (graph core1497) (root 9) 0 0 :=
  of_native_maps core1497 DegreeOneSmallSpectrum763.graph DegreeOneSmallSpectrum537.graph
    sourceMap1497 fusedMap1497 sourceMap1497_checked fusedMap1497_checked
    DegreeOneSmallComparisons.comparison1497
#print axioms sourceMap1497_checked
#print axioms fusedMap1497_checked
#print axioms certified1497
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
