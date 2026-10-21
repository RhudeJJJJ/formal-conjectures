/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1150 : Family 8 := level8.get ⟨192,by decide⟩
def sourceMap1150 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1150 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1150_checked : acceptsGraphIso
    (source (graph core1150) (root 8) 1 1) DegreeOneSmallSpectrum1575.graph sourceMap1150=true := by decide +kernel
theorem fusedMap1150_checked : acceptsGraphIso
    (fused (graph core1150) (root 8) 1 1) DegreeOneSmallSpectrum987.graph fusedMap1150=true := by decide +kernel
theorem certified1150 : Certified (graph core1150) (root 8) 1 1 :=
  of_native_maps core1150 DegreeOneSmallSpectrum1575.graph DegreeOneSmallSpectrum987.graph
    sourceMap1150 fusedMap1150 sourceMap1150_checked fusedMap1150_checked
    DegreeOneSmallComparisons.comparison1150
#print axioms sourceMap1150_checked
#print axioms fusedMap1150_checked
#print axioms certified1150
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
