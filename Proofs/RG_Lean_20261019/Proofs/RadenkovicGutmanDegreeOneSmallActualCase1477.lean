/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1477 : Family 9 := level9.get ⟨213,by decide⟩
def sourceMap1477 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1477 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1477_checked : acceptsGraphIso
    (source (graph core1477) (root 9) 0 0) SmallGeFourSpectrum159.graph sourceMap1477=true := by decide +kernel
theorem fusedMap1477_checked : acceptsGraphIso
    (fused (graph core1477) (root 9) 0 0) SmallGeFourSpectrum100.graph fusedMap1477=true := by decide +kernel
theorem certified1477 : Certified (graph core1477) (root 9) 0 0 :=
  of_native_maps core1477 SmallGeFourSpectrum159.graph SmallGeFourSpectrum100.graph
    sourceMap1477 fusedMap1477 sourceMap1477_checked fusedMap1477_checked
    DegreeOneSmallComparisons.comparison1477
#print axioms sourceMap1477_checked
#print axioms fusedMap1477_checked
#print axioms certified1477
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
