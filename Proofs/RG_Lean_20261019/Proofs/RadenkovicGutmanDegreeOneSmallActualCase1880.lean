/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1880 : Family 10 := level10.get ⟨146,by decide⟩
def sourceMap1880 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1880 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1880_checked : acceptsGraphIso
    (source (graph core1880) (root 10) 0 0) DegreeOneSmallSpectrum1289.graph sourceMap1880=true := by decide +kernel
theorem fusedMap1880_checked : acceptsGraphIso
    (fused (graph core1880) (root 10) 0 0) DegreeOneSmallSpectrum968.graph fusedMap1880=true := by decide +kernel
theorem certified1880 : Certified (graph core1880) (root 10) 0 0 :=
  of_native_maps core1880 DegreeOneSmallSpectrum1289.graph DegreeOneSmallSpectrum968.graph
    sourceMap1880 fusedMap1880 sourceMap1880_checked fusedMap1880_checked
    DegreeOneSmallComparisons.comparison1880
#print axioms sourceMap1880_checked
#print axioms fusedMap1880_checked
#print axioms certified1880
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
