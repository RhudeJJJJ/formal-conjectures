/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1034 : Family 8 := level8.get ⟨113,by decide⟩
def sourceMap1034 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap1034 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1034_checked : acceptsGraphIso
    (source (graph core1034) (root 8) 1 1) DegreeOneSmallSpectrum1801.graph sourceMap1034=true := by decide +kernel
theorem fusedMap1034_checked : acceptsGraphIso
    (fused (graph core1034) (root 8) 1 1) DegreeOneSmallSpectrum1124.graph fusedMap1034=true := by decide +kernel
theorem certified1034 : Certified (graph core1034) (root 8) 1 1 :=
  of_native_maps core1034 DegreeOneSmallSpectrum1801.graph DegreeOneSmallSpectrum1124.graph
    sourceMap1034 fusedMap1034 sourceMap1034_checked fusedMap1034_checked
    DegreeOneSmallComparisons.comparison1034
#print axioms sourceMap1034_checked
#print axioms fusedMap1034_checked
#print axioms certified1034
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
