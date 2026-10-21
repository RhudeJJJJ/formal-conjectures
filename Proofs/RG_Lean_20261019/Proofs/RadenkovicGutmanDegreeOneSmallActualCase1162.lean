/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1162 : Family 8 := level8.get ⟨199,by decide⟩
def sourceMap1162 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1162 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1162_checked : acceptsGraphIso
    (source (graph core1162) (root 8) 1 1) DegreeOneSmallSpectrum1644.graph sourceMap1162=true := by decide +kernel
theorem fusedMap1162_checked : acceptsGraphIso
    (fused (graph core1162) (root 8) 1 1) DegreeOneSmallSpectrum1016.graph fusedMap1162=true := by decide +kernel
theorem certified1162 : Certified (graph core1162) (root 8) 1 1 :=
  of_native_maps core1162 DegreeOneSmallSpectrum1644.graph DegreeOneSmallSpectrum1016.graph
    sourceMap1162 fusedMap1162 sourceMap1162_checked fusedMap1162_checked
    DegreeOneSmallComparisons.comparison1162
#print axioms sourceMap1162_checked
#print axioms fusedMap1162_checked
#print axioms certified1162
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
