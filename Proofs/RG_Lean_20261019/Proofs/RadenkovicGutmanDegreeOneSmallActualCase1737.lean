/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1737 : Family 9 := level9.get ⟨561,by decide⟩
def sourceMap1737 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1737 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1737_checked : acceptsGraphIso
    (source (graph core1737) (root 9) 0 0) DegreeOneSmallSpectrum842.graph sourceMap1737=true := by decide +kernel
theorem fusedMap1737_checked : acceptsGraphIso
    (fused (graph core1737) (root 9) 0 0) DegreeOneSmallSpectrum626.graph fusedMap1737=true := by decide +kernel
theorem certified1737 : Certified (graph core1737) (root 9) 0 0 :=
  of_native_maps core1737 DegreeOneSmallSpectrum842.graph DegreeOneSmallSpectrum626.graph
    sourceMap1737 fusedMap1737 sourceMap1737_checked fusedMap1737_checked
    DegreeOneSmallComparisons.comparison1737
#print axioms sourceMap1737_checked
#print axioms fusedMap1737_checked
#print axioms certified1737
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
