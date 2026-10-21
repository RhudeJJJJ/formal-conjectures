/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1010 : Family 8 := level8.get ⟨103,by decide⟩
def sourceMap1010 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 1 1 v)
def fusedMap1010 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1010_checked : acceptsGraphIso
    (source (graph core1010) (root 8) 1 1) DegreeOneSmallSpectrum1685.graph sourceMap1010=true := by decide +kernel
theorem fusedMap1010_checked : acceptsGraphIso
    (fused (graph core1010) (root 8) 1 1) DegreeOneSmallSpectrum1044.graph fusedMap1010=true := by decide +kernel
theorem certified1010 : Certified (graph core1010) (root 8) 1 1 :=
  of_native_maps core1010 DegreeOneSmallSpectrum1685.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1010 fusedMap1010 sourceMap1010_checked fusedMap1010_checked
    DegreeOneSmallComparisons.comparison1010
#print axioms sourceMap1010_checked
#print axioms fusedMap1010_checked
#print axioms certified1010
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
