/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1182 : Family 8 := level8.get ⟨230,by decide⟩
def sourceMap1182 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1182 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1182_checked : acceptsGraphIso
    (source (graph core1182) (root 8) 1 1) DegreeOneSmallSpectrum1891.graph sourceMap1182=true := by decide +kernel
theorem fusedMap1182_checked : acceptsGraphIso
    (fused (graph core1182) (root 8) 1 1) DegreeOneSmallSpectrum1292.graph fusedMap1182=true := by decide +kernel
theorem certified1182 : Certified (graph core1182) (root 8) 1 1 :=
  of_native_maps core1182 DegreeOneSmallSpectrum1891.graph DegreeOneSmallSpectrum1292.graph
    sourceMap1182 fusedMap1182 sourceMap1182_checked fusedMap1182_checked
    DegreeOneSmallComparisons.comparison1182
#print axioms sourceMap1182_checked
#print axioms fusedMap1182_checked
#print axioms certified1182
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
