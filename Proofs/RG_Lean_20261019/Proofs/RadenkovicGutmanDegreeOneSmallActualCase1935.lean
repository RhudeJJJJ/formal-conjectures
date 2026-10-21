/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1935 : Family 10 := level10.get ⟨229,by decide⟩
def sourceMap1935 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1935 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1935_checked : acceptsGraphIso
    (source (graph core1935) (root 10) 0 0) DegreeOneSmallSpectrum1148.graph sourceMap1935=true := by decide +kernel
theorem fusedMap1935_checked : acceptsGraphIso
    (fused (graph core1935) (root 10) 0 0) DegreeOneSmallSpectrum1157.graph fusedMap1935=true := by decide +kernel
theorem certified1935 : Certified (graph core1935) (root 10) 0 0 :=
  of_native_maps core1935 DegreeOneSmallSpectrum1148.graph DegreeOneSmallSpectrum1157.graph
    sourceMap1935 fusedMap1935 sourceMap1935_checked fusedMap1935_checked
    DegreeOneSmallComparisons.comparison1935
#print axioms sourceMap1935_checked
#print axioms fusedMap1935_checked
#print axioms certified1935
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
