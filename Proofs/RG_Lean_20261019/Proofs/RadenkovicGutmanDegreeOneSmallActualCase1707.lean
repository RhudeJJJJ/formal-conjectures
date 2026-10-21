/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1707 : Family 9 := level9.get ⟨487,by decide⟩
def sourceMap1707 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1707 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1707_checked : acceptsGraphIso
    (source (graph core1707) (root 9) 0 0) SmallGeFourSpectrum193.graph sourceMap1707=true := by decide +kernel
theorem fusedMap1707_checked : acceptsGraphIso
    (fused (graph core1707) (root 9) 0 0) SmallGeFourSpectrum192.graph fusedMap1707=true := by decide +kernel
theorem certified1707 : Certified (graph core1707) (root 9) 0 0 :=
  of_native_maps core1707 SmallGeFourSpectrum193.graph SmallGeFourSpectrum192.graph
    sourceMap1707 fusedMap1707 sourceMap1707_checked fusedMap1707_checked
    DegreeOneSmallComparisons.comparison1707
#print axioms sourceMap1707_checked
#print axioms fusedMap1707_checked
#print axioms certified1707
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
