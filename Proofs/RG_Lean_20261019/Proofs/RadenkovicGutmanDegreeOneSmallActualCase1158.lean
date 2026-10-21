/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1158 : Family 8 := level8.get ⟨197,by decide⟩
def sourceMap1158 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1158 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1158_checked : acceptsGraphIso
    (source (graph core1158) (root 8) 1 1) DegreeOneSmallSpectrum1627.graph sourceMap1158=true := by decide +kernel
theorem fusedMap1158_checked : acceptsGraphIso
    (fused (graph core1158) (root 8) 1 1) DegreeOneSmallSpectrum1010.graph fusedMap1158=true := by decide +kernel
theorem certified1158 : Certified (graph core1158) (root 8) 1 1 :=
  of_native_maps core1158 DegreeOneSmallSpectrum1627.graph DegreeOneSmallSpectrum1010.graph
    sourceMap1158 fusedMap1158 sourceMap1158_checked fusedMap1158_checked
    DegreeOneSmallComparisons.comparison1158
#print axioms sourceMap1158_checked
#print axioms fusedMap1158_checked
#print axioms certified1158
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
