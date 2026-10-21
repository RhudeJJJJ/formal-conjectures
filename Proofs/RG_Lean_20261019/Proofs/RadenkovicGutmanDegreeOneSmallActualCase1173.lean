/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1173 : Family 8 := level8.get ⟨210,by decide⟩
def sourceMap1173 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1173 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1173_checked : acceptsGraphIso
    (source (graph core1173) (root 8) 0 2) DegreeOneSmallSpectrum1743.graph sourceMap1173=true := by decide +kernel
theorem fusedMap1173_checked : acceptsGraphIso
    (fused (graph core1173) (root 8) 0 2) DegreeOneSmallSpectrum1090.graph fusedMap1173=true := by decide +kernel
theorem certified1173 : Certified (graph core1173) (root 8) 0 2 :=
  of_native_maps core1173 DegreeOneSmallSpectrum1743.graph DegreeOneSmallSpectrum1090.graph
    sourceMap1173 fusedMap1173 sourceMap1173_checked fusedMap1173_checked
    DegreeOneSmallComparisons.comparison1173
#print axioms sourceMap1173_checked
#print axioms fusedMap1173_checked
#print axioms certified1173
def sourceMap1173swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1173swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1173swap_checked : acceptsGraphIso
    (source (graph core1173) (root 8) 2 0) DegreeOneSmallSpectrum1743.graph sourceMap1173swap=true := by decide +kernel
theorem fusedMap1173swap_checked : acceptsGraphIso
    (fused (graph core1173) (root 8) 2 0) DegreeOneSmallSpectrum1090.graph fusedMap1173swap=true := by decide +kernel
theorem certified1173swap : Certified (graph core1173) (root 8) 2 0 :=
  of_native_maps core1173 DegreeOneSmallSpectrum1743.graph DegreeOneSmallSpectrum1090.graph
    sourceMap1173swap fusedMap1173swap sourceMap1173swap_checked fusedMap1173swap_checked
    DegreeOneSmallComparisons.comparison1173
#print axioms sourceMap1173swap_checked
#print axioms fusedMap1173swap_checked
#print axioms certified1173swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
