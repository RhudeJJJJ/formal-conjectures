/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1593 : Family 9 := level9.get ⟨334,by decide⟩
def sourceMap1593 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1593 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1593_checked : acceptsGraphIso
    (source (graph core1593) (root 9) 0 0) DegreeOneSmallSpectrum642.graph sourceMap1593=true := by decide +kernel
theorem fusedMap1593_checked : acceptsGraphIso
    (fused (graph core1593) (root 9) 0 0) SmallGeFourSpectrum133.graph fusedMap1593=true := by decide +kernel
theorem certified1593 : Certified (graph core1593) (root 9) 0 0 :=
  of_native_maps core1593 DegreeOneSmallSpectrum642.graph SmallGeFourSpectrum133.graph
    sourceMap1593 fusedMap1593 sourceMap1593_checked fusedMap1593_checked
    DegreeOneSmallComparisons.comparison1593
#print axioms sourceMap1593_checked
#print axioms fusedMap1593_checked
#print axioms certified1593
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
