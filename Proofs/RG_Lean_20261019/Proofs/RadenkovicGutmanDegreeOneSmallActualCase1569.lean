/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1569 : Family 9 := level9.get ⟨300,by decide⟩
def sourceMap1569 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,5,6,7,8,3,4] (sourceLabel 9 0 0 v)
def fusedMap1569 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1569_checked : acceptsGraphIso
    (source (graph core1569) (root 9) 0 0) SmallGeFourSpectrum149.graph sourceMap1569=true := by decide +kernel
theorem fusedMap1569_checked : acceptsGraphIso
    (fused (graph core1569) (root 9) 0 0) SmallGeFourSpectrum108.graph fusedMap1569=true := by decide +kernel
theorem certified1569 : Certified (graph core1569) (root 9) 0 0 :=
  of_native_maps core1569 SmallGeFourSpectrum149.graph SmallGeFourSpectrum108.graph
    sourceMap1569 fusedMap1569 sourceMap1569_checked fusedMap1569_checked
    DegreeOneSmallComparisons.comparison1569
#print axioms sourceMap1569_checked
#print axioms fusedMap1569_checked
#print axioms certified1569
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
