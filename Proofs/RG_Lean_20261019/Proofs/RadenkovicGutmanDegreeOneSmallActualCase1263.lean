/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1263 : Family 9 := level9.get ⟨43,by decide⟩
def sourceMap1263 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1263 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1263_checked : acceptsGraphIso
    (source (graph core1263) (root 9) 0 0) DegreeOneSmallSpectrum401.graph sourceMap1263=true := by decide +kernel
theorem fusedMap1263_checked : acceptsGraphIso
    (fused (graph core1263) (root 9) 0 0) SmallGeFourSpectrum094.graph fusedMap1263=true := by decide +kernel
theorem certified1263 : Certified (graph core1263) (root 9) 0 0 :=
  of_native_maps core1263 DegreeOneSmallSpectrum401.graph SmallGeFourSpectrum094.graph
    sourceMap1263 fusedMap1263 sourceMap1263_checked fusedMap1263_checked
    DegreeOneSmallComparisons.comparison1263
#print axioms sourceMap1263_checked
#print axioms fusedMap1263_checked
#print axioms certified1263
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
