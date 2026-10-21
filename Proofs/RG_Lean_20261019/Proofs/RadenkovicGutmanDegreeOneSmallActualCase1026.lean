/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1026 : Family 8 := level8.get ⟨110,by decide⟩
def sourceMap1026 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap1026 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1026_checked : acceptsGraphIso
    (source (graph core1026) (root 8) 1 1) DegreeOneSmallSpectrum1764.graph sourceMap1026=true := by decide +kernel
theorem fusedMap1026_checked : acceptsGraphIso
    (fused (graph core1026) (root 8) 1 1) DegreeOneSmallSpectrum1101.graph fusedMap1026=true := by decide +kernel
theorem certified1026 : Certified (graph core1026) (root 8) 1 1 :=
  of_native_maps core1026 DegreeOneSmallSpectrum1764.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1026 fusedMap1026 sourceMap1026_checked fusedMap1026_checked
    DegreeOneSmallComparisons.comparison1026
#print axioms sourceMap1026_checked
#print axioms fusedMap1026_checked
#print axioms certified1026
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
