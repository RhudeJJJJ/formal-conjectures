/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1493 : Family 9 := level9.get ⟨226,by decide⟩
def sourceMap1493 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1493 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1493_checked : acceptsGraphIso
    (source (graph core1493) (root 9) 0 0) DegreeOneSmallSpectrum761.graph sourceMap1493=true := by decide +kernel
theorem fusedMap1493_checked : acceptsGraphIso
    (fused (graph core1493) (root 9) 0 0) DegreeOneSmallSpectrum535.graph fusedMap1493=true := by decide +kernel
theorem certified1493 : Certified (graph core1493) (root 9) 0 0 :=
  of_native_maps core1493 DegreeOneSmallSpectrum761.graph DegreeOneSmallSpectrum535.graph
    sourceMap1493 fusedMap1493 sourceMap1493_checked fusedMap1493_checked
    DegreeOneSmallComparisons.comparison1493
#print axioms sourceMap1493_checked
#print axioms fusedMap1493_checked
#print axioms certified1493
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
