/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1275 : Family 9 := level9.get ⟨50,by decide⟩
def sourceMap1275 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1275 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1275_checked : acceptsGraphIso
    (source (graph core1275) (root 9) 0 0) DegreeOneSmallSpectrum437.graph sourceMap1275=true := by decide +kernel
theorem fusedMap1275_checked : acceptsGraphIso
    (fused (graph core1275) (root 9) 0 0) DegreeOneSmallSpectrum440.graph fusedMap1275=true := by decide +kernel
theorem certified1275 : Certified (graph core1275) (root 9) 0 0 :=
  of_native_maps core1275 DegreeOneSmallSpectrum437.graph DegreeOneSmallSpectrum440.graph
    sourceMap1275 fusedMap1275 sourceMap1275_checked fusedMap1275_checked
    DegreeOneSmallComparisons.comparison1275
#print axioms sourceMap1275_checked
#print axioms fusedMap1275_checked
#print axioms certified1275
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
