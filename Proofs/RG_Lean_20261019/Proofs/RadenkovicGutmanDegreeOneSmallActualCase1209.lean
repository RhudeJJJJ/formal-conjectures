/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1209 : Family 9 := level9.get ⟨7,by decide⟩
def sourceMap1209 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1209 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap1209_checked : acceptsGraphIso
    (source (graph core1209) (root 9) 0 0) DegreeOneSmallSpectrum371.graph sourceMap1209=true := by decide +kernel
theorem fusedMap1209_checked : acceptsGraphIso
    (fused (graph core1209) (root 9) 0 0) DegreeOneSmallSpectrum392.graph fusedMap1209=true := by decide +kernel
theorem certified1209 : Certified (graph core1209) (root 9) 0 0 :=
  of_native_maps core1209 DegreeOneSmallSpectrum371.graph DegreeOneSmallSpectrum392.graph
    sourceMap1209 fusedMap1209 sourceMap1209_checked fusedMap1209_checked
    DegreeOneSmallComparisons.comparison1209
#print axioms sourceMap1209_checked
#print axioms fusedMap1209_checked
#print axioms certified1209
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
