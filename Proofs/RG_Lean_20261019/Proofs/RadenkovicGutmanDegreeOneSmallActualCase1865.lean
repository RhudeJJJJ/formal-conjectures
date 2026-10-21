/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1865 : Family 10 := level10.get ⟨124,by decide⟩
def sourceMap1865 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1865 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1865_checked : acceptsGraphIso
    (source (graph core1865) (root 10) 0 0) DegreeOneSmallSpectrum1177.graph sourceMap1865=true := by decide +kernel
theorem fusedMap1865_checked : acceptsGraphIso
    (fused (graph core1865) (root 10) 0 0) DegreeOneSmallSpectrum949.graph fusedMap1865=true := by decide +kernel
theorem certified1865 : Certified (graph core1865) (root 10) 0 0 :=
  of_native_maps core1865 DegreeOneSmallSpectrum1177.graph DegreeOneSmallSpectrum949.graph
    sourceMap1865 fusedMap1865 sourceMap1865_checked fusedMap1865_checked
    DegreeOneSmallComparisons.comparison1865
#print axioms sourceMap1865_checked
#print axioms fusedMap1865_checked
#print axioms certified1865
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
