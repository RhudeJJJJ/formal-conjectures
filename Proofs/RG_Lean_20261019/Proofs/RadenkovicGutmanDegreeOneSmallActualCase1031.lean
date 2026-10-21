/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1031 : Family 8 := level8.get ⟨113,by decide⟩
def sourceMap1031 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap1031 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap1031_checked : acceptsGraphIso
    (source (graph core1031) (root 8) 0 0) DegreeOneSmallSpectrum286.graph sourceMap1031=true := by decide +kernel
theorem fusedMap1031_checked : acceptsGraphIso
    (fused (graph core1031) (root 8) 0 0) DegreeOneSmallSpectrum291.graph fusedMap1031=true := by decide +kernel
theorem certified1031 : Certified (graph core1031) (root 8) 0 0 :=
  of_native_maps core1031 DegreeOneSmallSpectrum286.graph DegreeOneSmallSpectrum291.graph
    sourceMap1031 fusedMap1031 sourceMap1031_checked fusedMap1031_checked
    DegreeOneSmallComparisons.comparison1031
#print axioms sourceMap1031_checked
#print axioms fusedMap1031_checked
#print axioms certified1031
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
