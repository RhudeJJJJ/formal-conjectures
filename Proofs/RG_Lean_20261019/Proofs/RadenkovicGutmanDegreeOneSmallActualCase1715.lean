/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1715 : Family 9 := level9.get ⟨495,by decide⟩
def sourceMap1715 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (sourceLabel 9 0 0 v)
def fusedMap1715 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1715_checked : acceptsGraphIso
    (source (graph core1715) (root 9) 0 0) SmallGeFourSpectrum139.graph sourceMap1715=true := by decide +kernel
theorem fusedMap1715_checked : acceptsGraphIso
    (fused (graph core1715) (root 9) 0 0) SmallGeFourSpectrum193.graph fusedMap1715=true := by decide +kernel
theorem certified1715 : Certified (graph core1715) (root 9) 0 0 :=
  of_native_maps core1715 SmallGeFourSpectrum139.graph SmallGeFourSpectrum193.graph
    sourceMap1715 fusedMap1715 sourceMap1715_checked fusedMap1715_checked
    DegreeOneSmallComparisons.comparison1715
#print axioms sourceMap1715_checked
#print axioms fusedMap1715_checked
#print axioms certified1715
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
