/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1457 : Family 9 := level9.get ⟨191,by decide⟩
def sourceMap1457 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1457 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1457_checked : acceptsGraphIso
    (source (graph core1457) (root 9) 0 0) DegreeOneSmallSpectrum714.graph sourceMap1457=true := by decide +kernel
theorem fusedMap1457_checked : acceptsGraphIso
    (fused (graph core1457) (root 9) 0 0) SmallGeFourSpectrum098.graph fusedMap1457=true := by decide +kernel
theorem certified1457 : Certified (graph core1457) (root 9) 0 0 :=
  of_native_maps core1457 DegreeOneSmallSpectrum714.graph SmallGeFourSpectrum098.graph
    sourceMap1457 fusedMap1457 sourceMap1457_checked fusedMap1457_checked
    DegreeOneSmallComparisons.comparison1457
#print axioms sourceMap1457_checked
#print axioms fusedMap1457_checked
#print axioms certified1457
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
