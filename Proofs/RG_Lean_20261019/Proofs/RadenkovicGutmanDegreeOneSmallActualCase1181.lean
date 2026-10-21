/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1181 : Family 8 := level8.get ⟨230,by decide⟩
def sourceMap1181 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1181 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1181_checked : acceptsGraphIso
    (source (graph core1181) (root 8) 0 2) DegreeOneSmallSpectrum1893.graph sourceMap1181=true := by decide +kernel
theorem fusedMap1181_checked : acceptsGraphIso
    (fused (graph core1181) (root 8) 0 2) DegreeOneSmallSpectrum1292.graph fusedMap1181=true := by decide +kernel
theorem certified1181 : Certified (graph core1181) (root 8) 0 2 :=
  of_native_maps core1181 DegreeOneSmallSpectrum1893.graph DegreeOneSmallSpectrum1292.graph
    sourceMap1181 fusedMap1181 sourceMap1181_checked fusedMap1181_checked
    DegreeOneSmallComparisons.comparison1181
#print axioms sourceMap1181_checked
#print axioms fusedMap1181_checked
#print axioms certified1181
def sourceMap1181swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1181swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1181swap_checked : acceptsGraphIso
    (source (graph core1181) (root 8) 2 0) DegreeOneSmallSpectrum1893.graph sourceMap1181swap=true := by decide +kernel
theorem fusedMap1181swap_checked : acceptsGraphIso
    (fused (graph core1181) (root 8) 2 0) DegreeOneSmallSpectrum1292.graph fusedMap1181swap=true := by decide +kernel
theorem certified1181swap : Certified (graph core1181) (root 8) 2 0 :=
  of_native_maps core1181 DegreeOneSmallSpectrum1893.graph DegreeOneSmallSpectrum1292.graph
    sourceMap1181swap fusedMap1181swap sourceMap1181swap_checked fusedMap1181swap_checked
    DegreeOneSmallComparisons.comparison1181
#print axioms sourceMap1181swap_checked
#print axioms fusedMap1181swap_checked
#print axioms certified1181swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
