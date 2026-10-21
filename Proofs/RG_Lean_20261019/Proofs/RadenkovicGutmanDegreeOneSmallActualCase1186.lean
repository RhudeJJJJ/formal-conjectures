/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1186 : Family 8 := level8.get ⟨232,by decide⟩
def sourceMap1186 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1186 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1186_checked : acceptsGraphIso
    (source (graph core1186) (root 8) 1 1) DegreeOneSmallSpectrum1901.graph sourceMap1186=true := by decide +kernel
theorem fusedMap1186_checked : acceptsGraphIso
    (fused (graph core1186) (root 8) 1 1) DegreeOneSmallSpectrum1297.graph fusedMap1186=true := by decide +kernel
theorem certified1186 : Certified (graph core1186) (root 8) 1 1 :=
  of_native_maps core1186 DegreeOneSmallSpectrum1901.graph DegreeOneSmallSpectrum1297.graph
    sourceMap1186 fusedMap1186 sourceMap1186_checked fusedMap1186_checked
    DegreeOneSmallComparisons.comparison1186
#print axioms sourceMap1186_checked
#print axioms fusedMap1186_checked
#print axioms certified1186
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
