/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1898 : Family 10 := level10.get ⟨172,by decide⟩
def sourceMap1898 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,8,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1898 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1898_checked : acceptsGraphIso
    (source (graph core1898) (root 10) 0 0) DegreeOneSmallSpectrum1101.graph sourceMap1898=true := by decide +kernel
theorem fusedMap1898_checked : acceptsGraphIso
    (fused (graph core1898) (root 10) 0 0) DegreeOneSmallSpectrum948.graph fusedMap1898=true := by decide +kernel
theorem certified1898 : Certified (graph core1898) (root 10) 0 0 :=
  of_native_maps core1898 DegreeOneSmallSpectrum1101.graph DegreeOneSmallSpectrum948.graph
    sourceMap1898 fusedMap1898 sourceMap1898_checked fusedMap1898_checked
    DegreeOneSmallComparisons.comparison1898
#print axioms sourceMap1898_checked
#print axioms fusedMap1898_checked
#print axioms certified1898
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
