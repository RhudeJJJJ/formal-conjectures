/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1926 : Family 10 := level10.get ⟨218,by decide⟩
def sourceMap1926 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1926 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1926_checked : acceptsGraphIso
    (source (graph core1926) (root 10) 0 0) DegreeOneSmallSpectrum1103.graph sourceMap1926=true := by decide +kernel
theorem fusedMap1926_checked : acceptsGraphIso
    (fused (graph core1926) (root 10) 0 0) DegreeOneSmallSpectrum1112.graph fusedMap1926=true := by decide +kernel
theorem certified1926 : Certified (graph core1926) (root 10) 0 0 :=
  of_native_maps core1926 DegreeOneSmallSpectrum1103.graph DegreeOneSmallSpectrum1112.graph
    sourceMap1926 fusedMap1926 sourceMap1926_checked fusedMap1926_checked
    DegreeOneSmallComparisons.comparison1926
#print axioms sourceMap1926_checked
#print axioms fusedMap1926_checked
#print axioms certified1926
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
