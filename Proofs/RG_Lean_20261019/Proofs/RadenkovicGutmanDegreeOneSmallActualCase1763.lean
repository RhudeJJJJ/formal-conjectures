/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1763 : Family 9 := level9.get ⟨649,by decide⟩
def sourceMap1763 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1763 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1763_checked : acceptsGraphIso
    (source (graph core1763) (root 9) 0 0) SmallGeFourSpectrum228.graph sourceMap1763=true := by decide +kernel
theorem fusedMap1763_checked : acceptsGraphIso
    (fused (graph core1763) (root 9) 0 0) SmallGeFourSpectrum178.graph fusedMap1763=true := by decide +kernel
theorem certified1763 : Certified (graph core1763) (root 9) 0 0 :=
  of_native_maps core1763 SmallGeFourSpectrum228.graph SmallGeFourSpectrum178.graph
    sourceMap1763 fusedMap1763 sourceMap1763_checked fusedMap1763_checked
    DegreeOneSmallComparisons.comparison1763
#print axioms sourceMap1763_checked
#print axioms fusedMap1763_checked
#print axioms certified1763
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
