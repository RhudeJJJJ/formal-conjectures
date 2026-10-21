/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1151 : Family 8 := level8.get ⟨196,by decide⟩
def sourceMap1151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (sourceLabel 8 0 0 v)
def fusedMap1151 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1151_checked : acceptsGraphIso
    (source (graph core1151) (root 8) 0 0) DegreeOneSmallSpectrum359.graph sourceMap1151=true := by decide +kernel
theorem fusedMap1151_checked : acceptsGraphIso
    (fused (graph core1151) (root 8) 0 0) DegreeOneSmallSpectrum245.graph fusedMap1151=true := by decide +kernel
theorem certified1151 : Certified (graph core1151) (root 8) 0 0 :=
  of_native_maps core1151 DegreeOneSmallSpectrum359.graph DegreeOneSmallSpectrum245.graph
    sourceMap1151 fusedMap1151 sourceMap1151_checked fusedMap1151_checked
    DegreeOneSmallComparisons.comparison1151
#print axioms sourceMap1151_checked
#print axioms fusedMap1151_checked
#print axioms certified1151
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
