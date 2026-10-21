/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1559 : Family 9 := level9.get ⟨290,by decide⟩
def sourceMap1559 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,8,9,10,11,1,2,3,7,5,6] (sourceLabel 9 0 0 v)
def fusedMap1559 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1559_checked : acceptsGraphIso
    (source (graph core1559) (root 9) 0 0) DegreeOneSmallSpectrum565.graph sourceMap1559=true := by decide +kernel
theorem fusedMap1559_checked : acceptsGraphIso
    (fused (graph core1559) (root 9) 0 0) DegreeOneSmallSpectrum561.graph fusedMap1559=true := by decide +kernel
theorem certified1559 : Certified (graph core1559) (root 9) 0 0 :=
  of_native_maps core1559 DegreeOneSmallSpectrum565.graph DegreeOneSmallSpectrum561.graph
    sourceMap1559 fusedMap1559 sourceMap1559_checked fusedMap1559_checked
    DegreeOneSmallComparisons.comparison1559
#print axioms sourceMap1559_checked
#print axioms fusedMap1559_checked
#print axioms certified1559
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
