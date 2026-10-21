/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1820 : Family 10 := level10.get ⟨64,by decide⟩
def sourceMap1820 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1820 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1820_checked : acceptsGraphIso
    (source (graph core1820) (root 10) 0 0) DegreeOneSmallSpectrum1162.graph sourceMap1820=true := by decide +kernel
theorem fusedMap1820_checked : acceptsGraphIso
    (fused (graph core1820) (root 10) 0 0) DegreeOneSmallSpectrum878.graph fusedMap1820=true := by decide +kernel
theorem certified1820 : Certified (graph core1820) (root 10) 0 0 :=
  of_native_maps core1820 DegreeOneSmallSpectrum1162.graph DegreeOneSmallSpectrum878.graph
    sourceMap1820 fusedMap1820 sourceMap1820_checked fusedMap1820_checked
    DegreeOneSmallComparisons.comparison1820
#print axioms sourceMap1820_checked
#print axioms fusedMap1820_checked
#print axioms certified1820
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
