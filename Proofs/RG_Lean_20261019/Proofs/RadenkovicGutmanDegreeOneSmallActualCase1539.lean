/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1539 : Family 9 := level9.get ⟨268,by decide⟩
def sourceMap1539 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1539 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1539_checked : acceptsGraphIso
    (source (graph core1539) (root 9) 0 0) SmallGeFourSpectrum154.graph sourceMap1539=true := by decide +kernel
theorem fusedMap1539_checked : acceptsGraphIso
    (fused (graph core1539) (root 9) 0 0) SmallGeFourSpectrum109.graph fusedMap1539=true := by decide +kernel
theorem certified1539 : Certified (graph core1539) (root 9) 0 0 :=
  of_native_maps core1539 SmallGeFourSpectrum154.graph SmallGeFourSpectrum109.graph
    sourceMap1539 fusedMap1539 sourceMap1539_checked fusedMap1539_checked
    DegreeOneSmallComparisons.comparison1539
#print axioms sourceMap1539_checked
#print axioms fusedMap1539_checked
#print axioms certified1539
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
