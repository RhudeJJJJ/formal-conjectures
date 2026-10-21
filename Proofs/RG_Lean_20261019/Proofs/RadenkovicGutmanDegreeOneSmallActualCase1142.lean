/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1142 : Family 8 := level8.get ⟨189,by decide⟩
def sourceMap1142 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1142 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1142_checked : acceptsGraphIso
    (source (graph core1142) (root 8) 1 1) DegreeOneSmallSpectrum1543.graph sourceMap1142=true := by decide +kernel
theorem fusedMap1142_checked : acceptsGraphIso
    (fused (graph core1142) (root 8) 1 1) DegreeOneSmallSpectrum980.graph fusedMap1142=true := by decide +kernel
theorem certified1142 : Certified (graph core1142) (root 8) 1 1 :=
  of_native_maps core1142 DegreeOneSmallSpectrum1543.graph DegreeOneSmallSpectrum980.graph
    sourceMap1142 fusedMap1142 sourceMap1142_checked fusedMap1142_checked
    DegreeOneSmallComparisons.comparison1142
#print axioms sourceMap1142_checked
#print axioms fusedMap1142_checked
#print axioms certified1142
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
