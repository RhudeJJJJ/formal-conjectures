/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1194 : Family 8 := level8.get ⟨264,by decide⟩
def sourceMap1194 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1194 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1194_checked : acceptsGraphIso
    (source (graph core1194) (root 8) 1 1) DegreeOneSmallSpectrum1992.graph sourceMap1194=true := by decide +kernel
theorem fusedMap1194_checked : acceptsGraphIso
    (fused (graph core1194) (root 8) 1 1) DegreeOneSmallSpectrum1521.graph fusedMap1194=true := by decide +kernel
theorem certified1194 : Certified (graph core1194) (root 8) 1 1 :=
  of_native_maps core1194 DegreeOneSmallSpectrum1992.graph DegreeOneSmallSpectrum1521.graph
    sourceMap1194 fusedMap1194 sourceMap1194_checked fusedMap1194_checked
    DegreeOneSmallComparisons.comparison1194
#print axioms sourceMap1194_checked
#print axioms fusedMap1194_checked
#print axioms certified1194
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
