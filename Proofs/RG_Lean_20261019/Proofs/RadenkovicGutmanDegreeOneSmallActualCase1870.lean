/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1870 : Family 10 := level10.get ⟨131,by decide⟩
def sourceMap1870 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1870 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1870_checked : acceptsGraphIso
    (source (graph core1870) (root 10) 0 0) DegreeOneSmallSpectrum1286.graph sourceMap1870=true := by decide +kernel
theorem fusedMap1870_checked : acceptsGraphIso
    (fused (graph core1870) (root 10) 0 0) DegreeOneSmallSpectrum957.graph fusedMap1870=true := by decide +kernel
theorem certified1870 : Certified (graph core1870) (root 10) 0 0 :=
  of_native_maps core1870 DegreeOneSmallSpectrum1286.graph DegreeOneSmallSpectrum957.graph
    sourceMap1870 fusedMap1870 sourceMap1870_checked fusedMap1870_checked
    DegreeOneSmallComparisons.comparison1870
#print axioms sourceMap1870_checked
#print axioms fusedMap1870_checked
#print axioms certified1870
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
